# Euler polynomials of line bundles on smooth proper schemes

`SmoothProperLineBundleEulerPolynomialStatement` concerns a field `K`, an
actual scheme `X` over `Spec K` that is smooth of relative dimension `g`,
proper and geometrically connected, and an actual line bundle `L` on `X`.
The field and schemes range over an arbitrary common universe. No algebraic
closure or characteristic restriction is imposed.

The assertion provides finite cohomology for every actual nonnegative tensor
power `Langlands.Scheme.Modules.tensorPow L.obj n`. Here finite cohomology means
that every actual derived cohomology object is a finite dimensional `K` vector
space and that these objects are zero in sufficiently high degrees; the bound
may depend on `n`. It also provides a polynomial `P` with rational coefficients
whose value at every natural `n`, including zero, is the integer Euler
characteristic of that tensor power, cast to the rationals. The Euler
characteristic uses the published alternating sum of the dimensions of the
actual derived cohomology objects, with the scalar action induced by `X.hom`.

The polynomial has natural degree at most `g`. When the published predicate
`L.IsAmple` holds, it has natural degree exactly `g` and strictly positive
leading coefficient. Positivity makes it nonzero, including when `g = 0`.
The assertion supplies the polynomial and the finiteness proofs; neither is
an input certificate. Ampleness retains its actual section-generation-locus
definition.

This is a derived specialization of the Stacks Project, Section 33.45
(tag `0BEL`), in the registered source
`stacks-numerical-intersections-finite-locally-free-rank-2026-10-31`,
file `0BEL.html`:

- Lemma 33.45.1 (tag `0BEM`), lines 163–169 and its proof, gives
  polynomiality of the Euler characteristic after tensoring a coherent
  sheaf with powers of invertible sheaves. Take the coefficient sheaf to be
  the structure sheaf and a single invertible sheaf `L`, and restrict the
  integer exponents to nonnegative integers.
- Lemma 33.45.9 (tag `0BEV`), lines 373–389, gives positivity for ample
  intersection numbers. Definition 33.45.10 and its following discussion
  (tag `0BEW`), lines 391–405, identify the leading coefficient of the
  single-variable Euler polynomial as the positive degree divided by `g!`.

The finite-cohomology clause is the proper coherent cohomology assertion
of Stacks Lemma 30.19.2 (tag `02O6`), together with bounded alternating
cohomology of a finite affine cover. The registered source
`stacks-very-ampleness-support-2026-10-29`, file `02O3.html`, lines 219–229,
contains the finite-generation assertion. A line bundle and each of its
tensor powers are coherent on this noetherian scheme. Properness gives a
finite affine cover and separatedness, so actual quasi-coherent cohomology
is computed by a bounded alternating Čech complex. The already developed
actual-cohomology comparisons give the same finite-cohomology predicate
used here.

Smooth geometric connectedness makes the nonempty scheme geometrically
integral, and its specified smooth relative dimension is its topological
dimension. These are the geometric specializations behind the degree
bound and the use of `X` itself in the positivity statement. The published
`SmoothProperConnectedFiniteFlatGeometryStatement`, applied to the identity
endomorphism, expresses these facts without additional assumptions.

This proposition is a numerical-geometry prerequisite. It asserts no
finite-map leading-coefficient comparison and no polarized native-rank
formula.
