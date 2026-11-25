# Archimedean idele invariants indexed by base places

This module is an internal derivation from the existing archimedean idele
invariant, actual idele automorphisms and completion maps, ordinary
inner-conjugation triviality on degree-two cohomology, and Mathlib's Galois
transitivity of infinite places. It makes no additional literature claim.

Let `F` and `E` be fields in one arbitrary universe `u`, with an `F`-algebra
structure on `E`, and suppose `E` is a number field. Write
`G = E ≃ₐ[F] E`. For `g ∈ G` and an infinite place `w` of `E`, the pullback
place `w' = infinitePlaceEquiv g.toRingEquiv w` is `g⁻¹ • w`.
The actual action on ideles transports the `w'` coordinate to the `w`
coordinate by the completion equivalence. Its complex realization preserves
`signClass`. This is
`signClass_ideleInfiniteCoordinate_relativeIdeleAut`.

The two stabilizers correspond by `c ↦ g⁻¹ c g`. Both membership and existence
of a nonidentity stabilizer element are proved to be equivalent. For an
ordinary idele two-cocycle `f`, apply the ordinary cohomology transformation
with group homomorphism `c ↦ g⁻¹ c g` and coefficient action by `g`. Its
`ideleConjugationValue` at `c` is the action by `g` on the original value at
`g⁻¹ c g`. The proof evaluates the actual cocycle map and uses additivity of
the coefficient action.

`archimedeanIdeleCocycleHom_innerConjugation` now compares the invariant
cocycle homomorphisms at `w` and `w'`. If the stabilizer contains a nonidentity
element, the evaluation formula for the existing invariant and the sign
identity prove the comparison. If it does not, both invariant values vanish.
Surjectivity and naturality of `H2π` descend this comparison to actual
`H²(G, J_E)`. The proved identity `innerConjugationMap_two_apply` then gives
`archimedeanIdeleInvariant_infinitePlaceEquiv`: the two invariants agree on
every cohomology class. These results do not require `E/F` to be Galois.

Now assume `IsGalois F E`. Infinite places with the same restriction to `F`
are conjugate, so `archimedeanIdeleInvariant_eq_of_comap_eq` proves that their
invariants agree. For each infinite place `v` of `F`,
`archimedeanIdeleInvariantAt v` is the additive homomorphism

`H²(Gal(E/F), J_E) →+ RationalModIntegers`

obtained by choosing a lift using `InfinitePlace.comap_surjective`.
`archimedeanIdeleInvariantAt_eq` proves equality with the invariant at any
infinite place `w` satisfying `w.comap (algebraMap F E) = v`. Thus the defined
homomorphism is independent of that choice.

With the additional instance `NumberField F`,
`archimedeanIdeleInvariantSum_eq` proves equality of the published sums for
any two families `wi` and `wi'` of infinite places above the base places.
It installs their lies-over witnesses, converts these to comap equalities,
and applies pointwise independence to the finite sum.

This supporting module concerns the archimedean part of idele cohomology.
It does not construct global invariants on idele-class cohomology or prove
`GlobalInvariantStatement`.
