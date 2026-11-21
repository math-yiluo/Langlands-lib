# A uniform equation bound on a fixed Hilbert-polynomial piece

`HasGeometricFibreHilbertPolynomial m J θ` is the affine test from
`HilbertSchemeUniversalFamilyStatement`, specialized to integral projective
`m`-space and its degree-one twist. Here `J` is an actual ideal sheaf on the
fibre product over `Spec (ULift ℤ)`. On each test over an algebraically closed
field, the degree-zero section rank of the `k`-th power of the restricted twist
is required to be `θ(k)` for all sufficiently large `k`. The threshold here
is allowed to depend on the test. `hilbertTwistPower` denotes exactly the
recursive tensor power used in the published test.

`exists_uniformBoundedHomogeneousEquations_of_hilbertPolynomial` gives a
single cutoff `D` once `m` and `θ` are fixed in the given universe. For every
commutative local ring in that universe and every such `J` whose subscheme is
flat and locally of finite presentation over the local base and satisfies the
test, its ideal in polynomial projective space has
`HasBoundedHomogeneousEquations` at `D`. In particular the bound is not tied
to a choice of field or a particular embedded family.

The proof uses the **published** Hilbert universal family for the native
`twistOne` and restricts its universal ideal to the open for `θ`. The open is
H-projective over the noetherian integral affine base, hence proper and
noetherian. Transport the restricted ideal to relative projective space and
apply the uniform bound for a noetherian family. Every tested ideal is
classified by a morphism to the Hilbert scheme by flatness and local finite
presentation, and the geometric section-rank test makes this map factor
through the chosen open. Naturality of the relative-projective comparison and
composition of ideal pullbacks identify its tested ideal with the pullback of
the bounded universal ideal, in the polynomial model.

This bound is a derived consequence of the published Hilbert-family and
bounded-equation theorems. It controls generators of the ideal *sheaf* on
standard affine charts; it asserts neither a regularity estimate nor an
explicit numeric bound. It does not construct a new Hilbert scheme.
