#! /usr/bin/env gforth
0 WARNINGS !

\ --------------------------------------------------------------
( global constants )

100000 constant divisor
divisor s>d d>f fconstant fdivisor
divisor divisor * constant divisor2

320 constant width
240 constant height
: image-size-text s" 320 240" ;

\ --------------------------------------------------------------
( Added 2021 to "ignore" divide by zero )

: */ dup 0= if drop 2drop divisor2 else */ then ;

\ --------------------------------------------------------------
( basic convenience words )

: 3dup   dup >r over >r >r over r> swap r> r> ;
: *!   swap over @ * swap ! ;
: */!   dup >r @ swap */ r> ! ;
: square   dup * ;
: square-d   dup divisor */ ;
: sign-d   divisor swap 0< if negate then ;

\ --------------------------------------------------------------
( integer powers )

: pow-d ( x e -- x^e )
    dup 0= if drop drop divisor exit then
    divisor swap 0 do over divisor */ divisor2 min loop nip ;

\ --------------------------------------------------------------
( integer square root )

: sqrt-step-d ( square guess -- square guess-delta )
    2dup divisor swap */ over - 2 / ;  ( NOTE: must be 2 /, not 2/ )
: sqrt-raw-d ( square -- root )
    1 begin sqrt-step-d dup abs 1 > while + repeat drop nip ;
: sqrt-d ( square -- root ) dup 0<= if drop 0 else sqrt-raw-d then ;

\ --------------------------------------------------------------
( cheat slightly on the one trig function we need )

variable cos-t
variable sin-t
: cos-sin ( t -- ) s>d d>f fdivisor f/ fdup
                   fcos fdivisor f* f>d drop cos-t !
                   fsin fdivisor f* f>d drop sin-t ! ;
: -cos-sin   negate cos-sin ;

\ --------------------------------------------------------------
( pi and radians )

31415926535 constant pi-numerator
10000000000 constant pi-denominator
: pi*   pi-numerator pi-denominator */ ;
: degrees ( rad[d]--deg )
          d>s pi-numerator pi-denominator 180 * */ ;

: 90degrees  90.00000 degrees ;
: -90degrees  -90.00000 degrees ;
: 180degrees  180.00000 degrees ;

\ --------------------------------------------------------------
( 3-vectors )

: vector   create 0 , 0 , 0 , ;
: vectors   3 * cells ;
: vdup   3dup ;
: vdrop   drop drop drop ;
: vx ;    : vy cell+ ;    : vz 2 cells + ;
: vx@ vx @ ;    : vy@ vy @ ;    : vz@ vz @ ;
: vx! vx ! ;    : vy! vy ! ;    : vz! vz ! ;
: vx+! vx +! ;    : vy+! vy +! ;    : vz+! vz +! ;
: vx*! vx *! ;    : vy*! vy *! ;    : vz*! vz *! ;
: vx*/! vx */! ;    : vy*/! vy */! ;    : vz*/! vz */! ;
: v!   dup >r vz! r>  dup >r vy! r>  vx! ;
: v@   dup >r vx@ r>  dup >r vy@ r>  vz@ ;
: vcopy   1 vectors move ;
: vaxis.   s>d tuck dabs
    <# # # # # # [char] . hold #s rot sign #> type space ;
: v.   >r >r vaxis. r> vaxis. r> vaxis. ;
: v#   d>s >r d>s >r d>s r> r> ;

\ --------------------------------------------------------------
( vector math )

: v+!   swap over vz+!  swap over vy+!  vx+! ;
: v*!   swap over vz*!  swap over vy*!  vx*! ;
: v*-d!   swap over divisor swap vz*/!
          swap over divisor swap vy*/!
                    divisor swap vx*/! ;
: vk*!   2dup vx*!  2dup vy*!  vz*! ;
: vk*/!   vdup vx*/!  vdup vy*/!  vz*/! ;
: vk*   swap over * >r  swap over * >r  *  r>  r> ;
: vk*/  2dup >r >r */ r> r> rot >r
        2dup >r >r */ r> r> rot >r
        */ r> r> ;
: v@@-   swap  2dup vz@ swap vz@ - >r
               2dup vy@ swap vy@ - >r
                    vx@ swap vx@ - r> r> ;
: v@+   swap over vz@ + >r  swap over vy@ + >r  vx@ + r> r> ;
: v+   >r >r swap >r swap >r + r> r> r> swap >r + r> r> + ;
: v-   >r >r swap >r swap >r - r> r> r> swap >r - r> r> - ;

\ --------------------------------------------------------------
( cross product )

: vcross   2dup vx@ swap vy@ * >r  2dup vy@ swap vx@ * r> - >r
           2dup vz@ swap vx@ * >r  2dup vx@ swap vz@ * r> - >r
           2dup vy@ swap vz@ * >r       vz@ swap vy@ * r> -
           r> r> ;
: vcross-d   vcross 1 divisor vk*/ ;

\ --------------------------------------------------------------
( vector rotation )

: 2d-rotate
    2dup sin-t @ divisor */ swap cos-t @ divisor */ swap - >r
         cos-t @ divisor */ swap sin-t @ divisor */ + r> swap ;
: vrotx   2d-rotate ;
: vroty   swap >r 2d-rotate r> swap ;
: vrotz   >r 2d-rotate r> ;
: vrotx!   dup >r v@ vrotx r> v! ;
: vroty!   dup >r v@ vroty r> v! ;
: vrotz!   dup >r v@ vrotz r> v! ;

\ --------------------------------------------------------------
( vector dot product and length )

: vdot   >r >r swap >r swap >r divisor */
         r> r> swap r> divisor */ swap r> divisor */ + + ;
: vlen2   vdup vdot ; \ square-d swap square-d + swap square-d + ;
: vunit   vdup vlen2 sqrt-d divisor swap vk*/ ;

\ --------------------------------------------------------------
( rays )

vector ray-origin
vector ray-direction
vector ray-up
vector ray-scale  ( only the first element )

: rays   3 * vectors ;
: ray-point   >r ray-direction v@ r> divisor vk*/
              ray-origin v@+ ;

\ --------------------------------------------------------------
( common vectors )

: x-axis   1.00000 0.00000 0.00000 v# ;
: y-axis   0.00000 1.00000 0.00000 v# ;
: z-axis   0.00000 0.00000 1.00000 v# ;
: -x-axis   -1.00000  0.00000  0.00000 v# ;
: -y-axis    0.00000 -1.00000  0.00000 v# ;
: -z-axis    0.00000  0.00000 -1.00000 v# ;

\ --------------------------------------------------------------
( stack of rays )

50 constant ray-stack-depth
here ray-stack-depth rays allot
variable ray-stack-start  ray-stack-start !
variable ray-stack-ptr   ray-stack-start @ ray-stack-ptr !

: vrpush ray-stack-ptr @ vcopy  1 vectors ray-stack-ptr +! ;
: vrpop -1 vectors ray-stack-ptr +!
    ray-stack-ptr @ swap vcopy ;

: r{   ray-origin vrpush ray-direction vrpush ray-up vrpush
       ray-scale vrpush ;
: }r   ray-scale vrpop
       ray-up vrpop ray-direction vrpop ray-origin vrpop ;

\ --------------------------------------------------------------
( ray frame transforms )

: translate   -1 vk* ray-origin v+! ;
: scale   swap 2dup ray-origin vk*/! ray-scale */! ;
: rotate-x   -cos-sin
    ray-origin vrotx!  ray-direction vrotx!  ray-up vrotx! ;
: rotate-y   -cos-sin
    ray-origin vroty!  ray-direction vroty!  ray-up vroty! ;
: rotate-z   -cos-sin
    ray-origin vrotz!  ray-direction vrotz!  ray-up vrotz! ;

\ --------------------------------------------------------------
( images, current fixed size only )

width height * 3 * constant image-bytes

: image   create here cell+ , image-bytes allot does> @ ;

variable target
variable color
: color!   color v! ;
: image-point   width * + 3 * ;
: color-clip   256 divisor */ 0 max 255 min ;
: plot   image-point target @ +
    color vz@ color-clip over 2 + c!
    color vy@ color-clip over 1+ c!
    color vx@ color-clip swap c! ;

\ --------------------------------------------------------------
( save an image )

variable image-file
: write-line-blind   image-file @ write-line drop ;
: save-image-file
    w/o bin create-file if
        abort" File not writeable" then image-file !
    s" P6"           write-line-blind
    s" # ppm file"   write-line-blind
    image-size-text  write-line-blind
    s" 255"          write-line-blind
    image-bytes image-file @ write-file drop
    image-file @ close-file drop ;

\ --------------------------------------------------------------
( load an image )

variable image-file
: skip-line   pad 40 image-file @ read-line drop drop drop ;
: load-image-file
    r/o bin open-file if
        abort" File not writeable" then image-file !
    skip-line skip-line skip-line skip-line
    image-bytes image-file @ read-file drop
    image-file @ close-file drop ;

\ --------------------------------------------------------------
( colors )

: black     0.00000 0.00000 0.00000 v# ;
: red       1.00000 0.00000 0.00000 v# ;
: orange    1.00000 0.75000 0.00000 v# ;
: yellow    1.00000 1.00000 0.00000 v# ;
: green     0.00000 1.00000 0.00000 v# ;
: cyan      0.00000 1.00000 1.00000 v# ;
: blue      0.00000 0.00000 1.00000 v# ;
: magenta   1.00000 0.00000 1.00000 v# ;
: white     1.00000 1.00000 1.00000 v# ;

\ : pink        1.00000 0.90000 0.90000 v# ;
\ : light-blue  0.90000 0.90000 1.00000 v# ;
: pink        1.00000 0.70000 0.70000 v# ;
: light-blue  0.70000 0.70000 1.00000 v# ;

\ --------------------------------------------------------------
( quadratic formula )

: discriminant-d ( abc--d ) swap square-d >r divisor */ 4 * r> swap - ;
: roots-d ( abc--xyn )
    >r 2dup r> discriminant-d
    dup 0< if drop drop drop 0 exit then
    dup 0= if drop negate swap 2* divisor swap */ 1 exit then
    sqrt-d dup >r >r negate 2dup
    r> - swap divisor swap */ 2/ r> swap >r + swap divisor swap */ 2/ r> 2 ;

\ --------------------------------------------------------------
( material stack )

variable material
50 constant material-stack-depth
here material-stack-depth cells allot
variable material-stack-start  material-stack-start !
variable material-stack-ptr
material-stack-start @ material-stack-ptr !

: m{   material @ material-stack-ptr @ !
       1 material-stack-ptr +! ;
: }m   -1 material-stack-ptr +!
       material-stack-ptr @ @ material ! ;

\ --------------------------------------------------------------
( handle ray target hits )

vector intercept  ( t u v )
vector intercept-n ( r u d )
variable intercept-material
variable intercept-limit
2000000000 constant hit-infinity
: hit-reset   hit-infinity intercept vx! ;
: hit?   intercept vx@ hit-infinity <> ;
: hit-t-cast   dup intercept vx@ < if
    intercept vx! material @ intercept-material ! 1
    else drop 0 then ;
: hit-t-shadow   intercept-limit @ < if 1 throw else 0 then ;
: hit-uv   intercept vy!  intercept vz! ;
: hit-n
    vdup ray-direction ray-up vcross-d vunit
        vdot intercept-n vx!
    vdup ray-up v@ vdot intercept-n vy!
        ray-direction v@ vdot intercept-n vz! ;

\ --------------------------------------------------------------
( select how to handle hits )

variable hit-handler

( pick either hit-t-shadow or hit-t-cast )
: hit-t   hit-handler @ execute ;

\ --------------------------------------------------------------
( intersection calculations )

vector normal
vector intersection

: compute-normal
    ray-direction ray-up vcross-d vunit
    intercept-n vx@ divisor vk*/
    ray-up v@ intercept-n vy@ divisor vk*/ v+
    ray-direction v@ intercept-n vz@ divisor vk*/ v+
    vunit
    normal v! ;

: compute-intersection
    ray-direction v@ intercept vx@ divisor vk*/
    ray-origin v@ v+
    intersection v! ;

: process-intersection compute-normal compute-intersection ;

\ --------------------------------------------------------------
( compute reflection off current intersection surface )

: reflect ( v -- v' )
    vdup normal v@ vdot 2*
    >r -1 vk* normal v@ r> divisor vk*/ v+ ;

\ --------------------------------------------------------------
( compute refraction off current intersection surface )

: refract ( v i -- v' )
    >r vdup normal v@ vdot dup square-d
    ( v v*N [v*N]^2 | i )
    divisor swap - r> dup >r square-d divisor */
    ( v v*N n^2*[1-[v*N]^2] | i )
    divisor swap - sqrt-d
    ( v v*N sqrt[1-n^2*[1-[v*N]^2]] | i )
    swap r> dup >r divisor */ + negate
    ( v -[v*N*n-sqrt[1-n^2*[1-[v*N]^2]]] | i )
    r> swap >r divisor vk*/ r>
    ( v*i -[v*N*n-sqrt[1-n^2*[1-[v*N]^2]]]*N )
    >r normal v@ r> divisor vk*/ v+
    ( v*i-[v*N*n-sqrt[1-n^2*[1-[v*N]^2]]]*N )
;

\ --------------------------------------------------------------
( find a vector perpendicular to another )

: perpendicular ( v -- v' )
    drop 2dup 0= swap 0= and if
      drop drop divisor divisor 0
    else
      swap negate 0 vunit
    then
;

\ --------------------------------------------------------------
( cast rays )

variable scene

: shadow-cast
    r{  ray-stack-ptr @  material-stack-ptr @
    ['] hit-t-shadow hit-handler !
    scene @ catch
    >r material-stack-ptr !  ray-stack-ptr !  }r  r> 0= ;

: ray-cast-winner   black color! hit? if
                       process-intersection
                       intercept-material @ execute
                    then ;

: ray-cast   hit-reset  ['] hit-t-cast hit-handler !
             r{ scene @ execute  }r ray-cast-winner ;

\ --------------------------------------------------------------
( lights )

20 constant light-limit
here light-limit vectors allot create light-position ,
here light-limit vectors allot create light-diffuse ,
here light-limit vectors allot create light-specular ,
here light-limit cells allot create light-visible ,

: i-light-position   vectors light-position + ;
: i-light-diffuse   vectors light-diffuse + ;
: i-light-specular   vectors light-specular + ;
: i-light-visible   cells light-visible + ;

variable gathering-lights
variable light-count

: reset-lights   0 light-count ! ;
: add-light ( vposition vcolor -- )
    gathering-lights @ if
      light-count @ i-light-specular v!
      light-count @ i-light-diffuse v!
      light-count @ i-light-position v!
      1 light-count +!
    else vdrop vdrop vdrop then ;

: gather-lights
    1 gathering-lights !  reset-lights
    hit-reset  ['] hit-t-cast hit-handler !
    r{ scene @ execute  }r
    0 gathering-lights ! ;

\ --------------------------------------------------------------
( check which lights are visible )

: shadow-check-one ( i -- )
    r{ dup i-light-position intersection v@@-
    vdup vlen2 sqrt-d dup intercept-limit ! divisor swap vk*/
    ray-direction v! intersection v@
    ray-direction v@ 100 divisor vk*/ v+
    ray-origin v!
    shadow-cast }r swap i-light-visible ! ;

: shadow-check   light-count @ 0 do i shadow-check-one loop ;

\ --------------------------------------------------------------
( diffuse )

: diffuse-one ( i -- )
    dup i-light-visible @ 0= if drop exit then
    dup i-light-position intersection v@@- vunit
    normal v@ vdot 0 max
    >r i-light-diffuse v@ r> divisor vk*/ color v+! ;

: diffuse   light-count @ 0 do i diffuse-one loop ;

\ --------------------------------------------------------------
( specular )

: specular-one ( i -- )
    dup i-light-visible @ 0= if drop exit then
    dup i-light-position intersection v@@- vunit
    reflect vunit ray-direction v@ vdot negate 0 max
    50 pow-d
    >r i-light-specular v@ r> divisor vk*/ color v+! ;

: specular   light-count @ 0 do i specular-one loop ;

\ --------------------------------------------------------------
( reflection )

variable bounces  0 bounces !
5 constant bounce-limit

: reflection   d>s
    bounces @ bounce-limit >= if drop exit then
    1 bounces +!
    >r color v@
    r{
    ray-direction v@ -1 vk* reflect  ray-direction v!
    intersection v@ ray-direction v@ 4 divisor vk*/ v+
    ray-origin v!
    ray-direction v@ perpendicular ray-up v!
    ray-cast
    }r
    r> divisor color vk*/!
    color v+!
    -1 bounces +!
;

\ --------------------------------------------------------------
( refraction )

: refraction ( i % -- ) d>s >r d>s r>
    bounces @ bounce-limit >= if drop drop exit then
    1 bounces +!
    >r >r color v@
    r{
    ray-direction v@ r> refract  ray-direction v!
    intersection v@ ray-direction v@ 4 divisor vk*/ v+
    ray-origin v!
    ray-direction v@ perpendicular ray-up v!
    ray-cast
    }r
    r> divisor color vk*/!
    color v+!
    -1 bounces +!
;

\ --------------------------------------------------------------
( unit-sphere intersection )

: sphere
   ( a ) divisor square-d
   ( b ) ray-direction v@ ray-origin v@ vdot 2*
   ( c ) ray-origin v@ vlen2 divisor -
   roots-d
   dup 0= if drop exit then
   2 = if nip then
   dup 0< if drop exit then
   dup divisor ray-scale @ */ hit-t if
      ray-point hit-n 0 0 hit-uv  ( TODO: add uv )
   else drop then ;

\ --------------------------------------------------------------
( bare-cylinder intersection )

: bare-cylinder ( h r -- ) swap >r >r
   ( a ) ray-direction vx@ square-d
         ray-direction vy@ square-d +
   ( b ) ray-direction vx@ ray-origin vx@ divisor */
         ray-direction vy@ ray-origin vy@ divisor */ + 2 *
   ( c ) ray-origin vx@ square-d
         ray-origin vy@ square-d +  r> square-d -
   roots-d
   dup 0= if rdrop drop exit then
   2 = if nip then
   dup 0< if rdrop drop exit then
   dup ray-direction vz@ divisor */ ray-origin vz@ +
   dup r> dup >r > if rdrop drop drop exit then
       r> negate < if drop exit then
   dup divisor ray-scale @ */ hit-t if
      ray-point drop 0 vunit
      hit-n 0 0 hit-uv  ( TODO: add uv )
   else drop then ;

\ --------------------------------------------------------------
( circle intersection )

: circle ( r -- ) >r
   ray-origin vz@ divisor ray-direction vz@ */ negate
   dup 0< if rdrop drop exit then
   dup ray-point drop
   square-d swap square-d + r> square-d > if drop exit then
   divisor ray-scale @ */
   hit-t if
     0 0 ray-direction vz@ sign-d  negate
     hit-n 0 0 hit-uv  ( TODO: add uv )
   then ;

: unit-circle divisor circle ;

\ --------------------------------------------------------------
( full cylinder )

: cylinder ( h r -- )
    r{ over 0 swap 0 swap translate dup circle }r
    r{ over negate 0 swap 0 swap translate
       180degrees rotate-x dup circle }r
    bare-cylinder ;

: unit-cylinder divisor divisor cylinder ;

\ --------------------------------------------------------------
( rectangle intersection )

: rectangle ( w h -- ) swap >r >r
   ray-origin vz@ divisor ray-direction vz@ */ negate
   dup 0< if rdrop rdrop drop exit then
   dup ray-point drop
   abs r> > if rdrop drop drop exit then
   abs r> > if drop exit then
   divisor ray-scale @ */
   hit-t if
     0 0 ray-direction vz@ sign-d negate
     hit-n 0 0 hit-uv  ( TODO: add uv )
   then ;

: square-shape divisor divisor rectangle ;

\ --------------------------------------------------------------
( rectangular prism / cube )

: rect-prism ( w h b -- )
    vdup r{        >r 0 0 r> translate rectangle }r
    vdup r{ negate >r 0 0 r> translate
            180degrees rotate-x rectangle }r
    vdup r{ >r swap r> swap        0 0 translate
            -90degrees rotate-y swap rectangle }r
    vdup r{ >r swap r> swap negate 0 0 translate
             90degrees rotate-y swap rectangle }r
    vdup r{ swap        >r 0 r> 0 translate
             90degrees rotate-x rectangle }r
         r{ swap negate >r 0 r> 0 translate
             -90degrees rotate-x rectangle }r
;

: cube   divisor divisor divisor rect-prism ;

\ --------------------------------------------------------------
( handle camera )

vector camera-eye
vector camera-target
vector camera-up

variable camera-hspan   variable camera-vspan
vector viewport-in
vector viewport-right
vector viewport-up

0.00000 0.00000  0.00000 v# camera-target v!
0.00000 0.00000  10.00000 v# camera-eye v!
0.00000 1.00000  0.00000 v# camera-up v!
5.00000 d>s camera-vspan !
camera-vspan @ width height */ camera-hspan !

: camera-init
   divisor ray-scale !
   camera-eye ray-origin vcopy
   camera-target camera-eye v@@- vunit viewport-in v!
   viewport-in camera-up vcross-d vunit viewport-right v!
   viewport-right viewport-in vcross-d vunit viewport-up v!
   camera-hspan @ divisor viewport-right vk*/!
   camera-vspan @ divisor viewport-up vk*/!  ;
: camera-ray ( ij-- ) height 2/ - negate >r width 2/ - >r
   camera-target ray-direction vcopy
   viewport-right v@ r> width vk*/ ray-direction v+!
   viewport-up v@ r> height vk*/ ray-direction v+!
   ray-direction ray-origin v@@- vunit ray-direction v!
   ray-direction v@ perpendicular ray-up v! ;

\ --------------------------------------------------------------
( render a frame )

: cast-one   2dup camera-ray ray-cast plot ;
: frame   camera-init gather-lights
          height 0 do width 0 do i j
          cast-one loop i . loop cr ;

\ --------------------------------------------------------------
( phong sample )

: sample-green
                 shadow-check
                 diffuse
                 green white v+ 1 2 vk*/ color v*-d!
                 specular
                 0.02500 0.05000 0.02500 v# color v+!
;

: scene1
  ['] sample-green material !
  2 1 scale
  sphere
;

\ --------------------------------------------------------------
( phong sample )

: mirror
    shadow-check diffuse
      1 8 color vk*/! specular 0.75000 reflection ;
: glass
    shadow-check diffuse
      1 2 color vk*/! specular 0.75000 reflection
                       0.33333 0.75000 refraction ;
: plastic   shadow-check diffuse specular
      0.50000 reflection ;
: matte   shadow-check diffuse ;
: debug-material   normal v@ abs >r abs >r abs r> r> color! ;

variable angle

: scene2
20.00000 10.00000 20.00000 v#
pink 1 2 vk*/  white 1 3 vk*/   add-light
-20.00000 10.00000 20.00000 v#
light-blue 1 2 vk*/  white 1 3 vk*/   add-light
['] plastic material !
r{ angle @ rotate-y
r{
  r{ m{ ['] mirror material !
    2 1 scale
    unit-circle
  }m }r
  r{
    r{
      2.50000 0.00000 0.00000 v# translate
      4 3 scale
      unit-cylinder
    }r
    r{
      2.50000 0.00000 2.00000 v# translate
      1 2 scale
      sphere
    }r
  }r
}r
r{
  0.00000 0.00000 1.00000 v# translate
  r{
    0.00000 0.50000 0.00000 v# translate
    sphere
  }r
  r{
    0.00000 -0.50000 0.00000 v# translate
    sphere
  }r
  r{ m{ ['] glass material !
    -45.00000 degrees rotate-y
    -1.00000 0.00000 1.00000 v# translate
    3 8 scale
    sphere
  }m }r
}r
}r
;


\ --------------------------------------------------------------
( FIG )

: red-plastic   shadow-check diffuse  red color v*-d!
      specular 0.50000 reflection ;
: green-glass   shadow-check diffuse  green 1 3 vk*/ color v*-d!
      specular 0.33333 reflection
      0.33333 0.33333 refraction ;
: blue-plastic   shadow-check diffuse  blue color v*-d!
      specular 0.50000 reflection ;

: letter-F m{ r{ ['] red-plastic material !
              r{ -1.00000 0.00000 0.00000 v# translate
                  0.20000 1.15000 0.20000 v# rect-prism }r
              r{ 0.00000 1.00000 0.00000 v# translate
                 1.15000 0.20000 0.20000 v# rect-prism }r
              r{ -0.30000 0.00000 0.00000 v# translate
                 0.70000 0.20000 0.20000 v# rect-prism }r
           }r }m ;

: letter-I m{ r{ ['] green-glass material !
             r{ 0.00000 0.80000 0.00000 v# translate
                1 2 scale sphere }r
             r{ 0.00000 -0.40000 0.00000 v# translate
                90.00000 degrees rotate-x
                0.60000 d>s 0.30000 d>s cylinder }r
           }r }m ;

: letter-G m{ r{ ['] blue-plastic material !
              r{ -1.00000 0.00000 0.00000 v# translate
                  0.20000 1.10000 0.20000 v# rect-prism }r
              r{ 1.00000 -0.50000 0.00000 v# translate
                  0.20000 0.50000 0.20000 v# rect-prism }r
              r{ 0.00000 1.00000 0.00000 v# translate
                 1.10000 0.20000 0.20000 v# rect-prism }r
              r{ 0.00000 -1.00000 0.00000 v# translate
                 1.10000 0.20000 0.20000 v# rect-prism }r
              r{ 0.50000 0.00000 0.00000 v# translate
                 0.50000 0.20000 0.20000 v# rect-prism }r
           }r }m ;

: fig r{
  r{ -2.00000 1.00000 0.00000 v# translate letter-F }r
  r{  0.00000 0.50000 0.00000 v# translate letter-I }r
  r{  2.00000 0.00000 0.00000 v# translate letter-G }r
}r ;

: floor r{ m{
  ['] mirror material !
  0.00000 -1.40000 0.00000 v# translate
  90.00000 degrees rotate-x
  3 1 scale
  unit-circle
}m }r ;

: fig-background
  r{ m{ ['] blue-plastic material !
    -1.30000 1.00000 -1.00000 v# translate sphere }m }r
  r{ m{ ['] red-plastic material !
    1.30000 1.00000 -1.00000 v# translate sphere }m }r
  r{ m{ ['] plastic material !
    0.00000 1.00000 -2.00000 v# translate sphere }m }r
  r{ m{ ['] glass material !
    0.00000 2.00000 -3.00000 v# translate sphere }m }r
;

: fig-scene
  20.00000 10.00000 20.00000 v#
  pink 1 2 vk*/  white 1 3 vk*/   add-light
  -20.00000 10.00000 20.00000 v#
  light-blue 1 2 vk*/  white 1 3 vk*/   add-light
  r{
    angle @ rotate-y
    fig-background
    fig
    floor
  }r
;

\ --------------------------------------------------------------
( pick filename )

: s>str s>d <# #s #> ;
: scat >r >r 2dup + r> swap r> dup >r move r> + ;
: pick-filename s>str s" .ppm" scat ;

\ --------------------------------------------------------------
( main )

image main-image
main-image target !

: go
  0.00000 0.00000 0.00000 v# camera-target v!
  -6.00000 3.00000 10.00000 v# camera-eye v!

\  ['] scene1 scene !
\  frame
\  main-image s" out.ppm" save-image-file

  ['] fig-scene scene !
  frame
  main-image s" fig.ppm" save-image-file

\  ['] scene2 scene !
\  360 0 do i divisor * s>d degrees angle !
\    frame
\    main-image i pick-filename save-image-file
\  loop

  bye
;
go

\ --------------------------------------------------------------

