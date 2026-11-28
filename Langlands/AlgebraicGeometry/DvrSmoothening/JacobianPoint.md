# The Jacobian criterion at a point for a quotient of a polynomial ring

- `isLocalization_quotient`: localization commutes with quotients.
- `injective_of_span_eq_top_of_linearIndependent`: a linear map out of a span of a finite family
  with independent image is injective.
- `formallySmooth_quotient_of_linearIndependent`: **Jacobian criterion.** If `P` is formally
  smooth over `R` with finite free differentials and `f₁, …, f_c` vanish at a point `P → L` of a
  field with linearly independent `1 ⊗ dfᵢ ∈ L ⊗ Ω_P`, then the localization of `P` at the kernel
  divided by the `fᵢ` is formally smooth over `R` (Mathlib's
  `Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange`).
- `exists_relations_linearIndependent`: for a surjection `P → A` and a field `L` over `A` such that
  `L ⊗_P Ω_{P/R}` is finite-dimensional over `L`, there are relations with independent
  differentials whose number is at least `dim L ⊗ Ω_P − dim L ⊗ Ω_A` (conormal sequence).
- `ker_eq_bot_of_finrank_le`: a surjection `C → A` of local formally smooth algebras, with `C`
  noetherian with finite free differentials, that does not drop the dimension of the differentials
  at the closed point is injective (Jacobian criterion and Nakayama's lemma).
- `finrank_tensor_kaehler_eq`, `free_kaehler_of_formallySmooth`,
  `finrank_add_le_of_linearIndependent`: rank computations for differentials.
- `isSmoothAt_of_le`: for a finitely presented algebra, smoothness at a prime passes to smaller
  primes.

Used in the proof of `DefectZeroSmoothAtStatement` (module `DefectZero`).
