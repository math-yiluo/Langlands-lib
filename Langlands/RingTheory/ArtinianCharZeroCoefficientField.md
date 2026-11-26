# Coefficient fields of local Artinian `ℚ`-algebras

Module `Langlands.RingTheory.ArtinianCharZeroCoefficientField`, namespace
`Langlands.RingTheory`. `R` is a commutative local Artinian ring in an arbitrary universe.

- `isNilpotent_ker_residue R`: the kernel of the residue map `R → ResidueField R`, the
  maximal ideal, is nilpotent. It is the Jacobson radical of `R`, which is nilpotent for
  Artinian rings (Mathlib's `IsArtinianRing.isNilpotent_jacobson_bot`).
- `charZero_residueField R`: if `R` is a `ℚ`-algebra, its residue field has characteristic
  zero, since it receives a ring homomorphism from `ℚ`.
- `exists_coefficientField R`: if `R` is a `ℚ`-algebra, there is a ring homomorphism
  `σ : ResidueField R →+* R` with `residue R ∘ σ = id`. The residue field has
  characteristic zero, so it is formally smooth over `ℤ` (the published
  `Langlands.GroupScheme.IntegralModel.formallySmooth_int_of_charZero`). Formal smoothness
  lifts the identity of the residue field through the surjection `R → ResidueField R`
  with nilpotent kernel (Mathlib's `Algebra.FormallySmooth.liftOfSurjective`).

## Provenance

Internal derived content: the existence of coefficient fields in equal characteristic
zero, as recalled in the statement Markdown of
`Langlands.AbelianScheme.AbelianArtinianLiftingStatement`, obtained here exactly as in
the published `exists_coefficientField_of_charZero` for congruence quotients.
