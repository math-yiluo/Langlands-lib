# Tangents of all-test fixed subgroups

This derived development compares the actual all-refinement fixed subgroup
with differential invariants, using the existing automorphic action and
dual-number Lie module. Its constructions and proofs are internal consequences
of those APIs and the affine-cover and trivial-square-zero-extension APIs.
They use no unproved representability or smoothness statement.

For a commutative ring object `R`, an affine group scheme `G` over `Spec R`,
an arbitrary group scheme `H`, and an actual automorphic action `a` of `H`
on `G`, `AutomorphicAction.lieInvariants a` is the submodule of
`Additive (lieKernel G R)` consisting of vectors whose change to every
commutative `R`-algebra `A` is fixed by `a.differential h` for every actual
`A`-point `h` of `H`. The differential is the existing linear action obtained
by acting with the constant lift of `h` on the dual-number identity kernel.
Coefficient change is semilinear, and the differential is linear over `A`;
these facts prove the submodule laws.

The implemented comparison is
`AutomorphicAction.isFixed_iff_mem_lieInvariants`: the underlying
dual-number point of a tangent vector is fixed on every scheme refinement
if and only if the vector belongs to this invariant submodule.
No affineness or smoothness assumption is made on `H`.

The forward proof applies all-refinement invariance to the dual-number
coefficient map and the constant lift of each acting point, then uses
injectivity of the underlying subtype and additive-to-multiplicative maps.
The reverse proof first reduces to affine refinements by
`AutomorphicAction.isFixed_of_affine`. That criterion restricts an arbitrary
scheme refinement to its affine open cover, identifies each member with an
algebra spectrum, and checks equality on the cover.

For an affine refinement, its algebra map `f : DualNumber R →ₐ[R] A`
sends epsilon to a square-zero element `e`. The actual algebra map
`Lie.epsilonSpecialization e he : DualNumber A →ₐ[R] A` sends
`x + epsilon*y` to `x + e*y`; it fixes constant coefficients.
`Lie.epsilonSpecialization_comp_coefficients` proves that `f` is the
coefficient map followed by this specialization, by algebra-map extensionality
and the identity `epsilon*r = r • epsilon`.
Applying specialization to the assumed differential invariant equation gives
the action invariant equation on the affine refinement. Naturality of the
original action and both composition identities identify its two sides.
The affine-cover criterion then gives invariance on every scheme refinement.

For any field `k`, affine `G`, commutative group scheme `T`, morphism
`i : T.toGrp ⟶ G`, and character `a`, the theorem
`RelativeRoot.lieInvariants_kernelConjugation` identifies the invariants of
conjugation restricted to the actual character kernel with the existing
`RelativeRoot.kernelLieInvariants i a`. It uses the published differential
restriction and conjugation identities. Thus
`RelativeRoot.kernelCentralizer_hasLieImage` proves
`HasLieImage (kernelCentralizer i a) (kernelLieInvariants i a)`.

All constructions retain universe `u` and all coefficient algebras in that
universe. The character need not be nonzero or primitive, `T` need not be split,
and its character kernel need not be smooth or reduced. The comparison proves
the invariant tangent image; identifying that submodule with the integral
weight span and constructing a smooth closed representative remain separate
obligations.
