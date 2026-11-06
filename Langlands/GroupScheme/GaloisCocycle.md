# Scheme cocycles and Galois cohomology

This derived interface compares the existing all-test-schemes cocycles with
ordinary group cohomology of actual affine points. All fields and coefficient
points are in an arbitrary common universe `u`.

For an extension `L/k`, `cover k L` is the actual `k`-scheme `Spec L`, and
`arrow k L σ` is the scheme endomorphism induced by the `k`-algebra
automorphism `σ` of `L`. The definition `value ξ σ` evaluates the scheme
cocycle on the identity and this endomorphism. Naturality and the scheme
cocycle identity prove
`value ξ (σ * τ) = value ξ σ * σ(value ξ τ)`, where the coefficient action
is the actual conjugation map from `GaloisPointDescent`. Evaluating a scheme
coboundary gives the convention `f * (σ f)⁻¹`. These facts do not require a
commutative group scheme.

Assume now that `L/k` is finite Galois. The theorem
`toFun_eq_of_value_eq` shows that these values determine the cocycle on
every relative test scheme. Its proof evaluates both cocycles on the two
universal projections from `Spec L × Spec L`. The published finite Galois
overlap decomposition identifies that overlap with a coproduct of copies
of `Spec L`, indexed by the field automorphisms. Naturality identifies the
restriction to each component with the corresponding `value`. The
coproduct isomorphism detects equality on the overlap. Pullback
universality and naturality then give equality for every pair of maps
from every test scheme.

Consequently, `isTrivial_iff` identifies scheme triviality with the
existence of an actual point `f` over the same field `L` satisfying
`value ξ σ = f * (σ f)⁻¹` for every automorphism. The reverse implication
compares the cocycle with the actual scheme coboundary of `f`, using the
all-test detection theorem. It does not replace the original cocycle
notion by a condition on field-valued points.

For a commutative group scheme, `pointRepresentation` equips the additive
form of its actual affine `L`-points with the actual Galois action and
scalars `ULift.{u} ℤ`. Its action is the integral linear map induced by
conjugation, with scalars restricted to the lifted integers.
`additiveCocycle` converts the crossed multiplicative identity into
Mathlib's ordinary additive degree-one cocycle convention; commutativity
allows the order of the two terms to be exchanged.

Finally, `isTrivial_of_H1_isZero` says that vanishing of ordinary first
cohomology of this representation trivializes every scheme cocycle on
this finite Galois cover. Mathlib's degree-one quotient criterion supplies
an additive cochain `x` with `σ x - x = value ξ σ`. Its multiplicative
form is `σ z * z⁻¹ = value ξ σ`. Choosing the scheme cochain `z⁻¹` gives
the required coboundary convention, and `isTrivial_iff` concludes
triviality on all test schemes.

The provenance is internal: the module derives these comparisons from
`TorsorCocycle`, `GaloisPointDescent`, `Descent.FiniteGaloisTensor`, and
Mathlib's existing degree-one group-cohomology objects and quotient
criterion. It proves no unconditional cohomology vanishing, torus tensor
identification, or quasi-splitness theorem.
