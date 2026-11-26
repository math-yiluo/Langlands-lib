# The image of absolute Galois restriction along a closure embedding

Module `Langlands.Galois.HeckeInduction.RestrictionIndex`, name space
`Langlands.GaloisRepresentation`. Let `K` and `E` be fields with a `K`-algebra structure on `E`
and `e : AlgebraicClosure K →ₐ[K] AlgebraicClosure E` a closure embedding. The map
`restrictionAlongClosure e : Gal(Ē/E) → Gal(K̄/K)` is the one of
`Langlands.Galois.ClosureRestriction`, characterised by `e (r(s) x) = s (e x)`.

## Algebraic extensions

Assume `Algebra.IsAlgebraic K E`.

- `closureEmbedding_bijective`: `e` is bijective, since `Ē` is algebraic over `K`
  (`Algebra.IsAlgebraic.algHom_bijective₂` with Mathlib's `IsAlgClosed.lift` in the other
  direction). `closureEmbeddingEquiv e` is `e` as an isomorphism of `K`-algebras.
- `transportedEmbedding e : E →ₐ[K] K̄` is `e⁻¹` composed with `E → Ē`
  (`e_transportedEmbedding`), and `transportedField e` is its field range.
- `restrictionAlongClosure_injective`: restriction along `e` is injective, because `e` is
  surjective.
- `mem_range_restrictionAlongClosure_iff`: `g ∈ Gal(K̄/K)` is in the image if and only if `g`
  fixes `transportedEmbedding e x` for every `x : E`. For the converse, `e ∘ g ∘ e⁻¹` fixes `E`
  and restricts to `g`.
- `absoluteToGal K` is the identity homomorphism from `Field.absoluteGaloisGroup K` to
  `Gal(AlgebraicClosure K/K)`. `range_restrictionAlongClosure_eq` identifies the image with the
  preimage of `(transportedField e).fixingSubgroup` under it.
- `descendedCharacter e ψ` is the homomorphism on the image corresponding to a homomorphism `ψ`
  on `Gal(Ē/E)` (through `MonoidHom.ofInjective`); `descendedCharacter_comp_rangeRestrict`
  states `(descendedCharacter e ψ).comp (restrictionAlongClosure e).toMonoidHom.rangeRestrict
  = ψ`, and `descendedCharacter_apply` evaluates it on `restrictionAlongClosure e s`.

## Finite extensions

Assume `FiniteDimensional K E` and `IsGalois K (AlgebraicClosure K)`.

- `finrank_transportedField`: `[transportedField e : K] = [E : K]`.
- `index_range_restrictionAlongClosure`: the image has index `[E : K]`, by Mathlib's
  `IntermediateField.finrank_eq_fixingSubgroup_index` for the Galois extension `K̄/K`.
- `finiteIndex_range_restrictionAlongClosure`: the image has finite index.
- `isOpen_range_restrictionAlongClosure`, for `IsGalois E (AlgebraicClosure E)`: the image is
  open. It is compact, the continuous image of the profinite group `Gal(Ē/E)`, hence closed in
  the Hausdorff group `Gal(K̄/K)`, and a closed subgroup of finite index is open.
- `continuous_descendedCharacter`, for `IsGalois E (AlgebraicClosure E)`: the descended
  homomorphism of a continuous `ψ` is continuous on the image with its subspace topology, since a
  continuous bijection from a compact space onto a Hausdorff space has continuous inverse
  (`Continuous.continuous_symm_of_equiv_compact_to_t2`).

For number fields all these hypotheses hold by Mathlib instances.

## Provenance

This is a derived, internal module. It describes the image of the absolute Galois group of a
finite extension under restriction along a specified closure embedding, the Galois-theoretic
fact that this image is the fixing group of a conjugate copy of `E`, of index `[E : K]`.
The implemented proofs are those described above.
