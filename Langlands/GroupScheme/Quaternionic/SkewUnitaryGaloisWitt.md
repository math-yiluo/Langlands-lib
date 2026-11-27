# Proper Witt transitivity over every field extension

Module: `Langlands.GroupScheme.Quaternionic.SkewUnitaryGaloisWitt`.

Let `F` have characteristic zero, `D` be a central quaternion division algebra over `F` with
an involution `σ` of the first kind with `dim D^σ = 3`, and `τ = σ.quaternionConjugation`.

- `coefficientAlgEquiv K N`: the comparison `K ⊗[F] M_N(D) ≃ M_N(K ⊗[F] D)` of
  `coefficientEquiv` as an isomorphism of `K`-algebras.
- `reducedNorm_matrix_baseChange`: for a matrix `p` over `K ⊗ D`, the reduced norm of `p` in
  the central simple `K`-algebra `M_N(K ⊗ D)` equals `matrixReducedNorm K p`, the reduced
  norm of the `F`-algebra `M_N(D)` extended to `K`. Proof: `reducedNorm_algEquiv` along
  `coefficientAlgEquiv` and `reducedNorm_baseChange` for the central simple algebra
  `M_N(D)`.
- `properWittAt_of_split`: if `K ⊗ D ≅ M_2(K)`, `ProperWittAt τ K N` for `N ≥ 2` is
  `quaternionicProperWittSplit`.
- `properWittAt_of_isDomain`: if `K ⊗ D` is a domain (hence a division algebra), apply
  `exists_properIsometry_skewGram_division` to `K ⊗ D` with the involution
  `σ.baseChange K` (its symmetric part has dimension `3`,
  `finrank_symmetricSubspace_baseChange`). Its quaternion conjugation equals
  `τ.baseChange K`: both are conjugation of `σ.baseChange K` by a nonzero element of the
  one-dimensional alternating line of `σ.baseChange K`, which differ by a nonzero scalar
  (`BinaryAction.quaternionConjugation_baseChange`,
  `finrank_alternatingSubspace_of_dimensions`). The reduced norm condition is converted by
  `reducedNorm_matrix_baseChange`.
- `properWittAt`: for every field `K ⊇ F` of characteristic zero and `N ≥ 2`, by the
  dichotomy `quaternionCoefficientDichotomy` (`K ⊗ D` is a domain or `M_2(K)`).

Proper unitary transitivity on rows with a common invertible value is Kneser, *Lectures on
Galois Cohomology of Classical Groups* (TIFR Lectures on Mathematics 47, 1969), §2.6, Lemma 2,
printed pp. 32–33, used in §5.11, printed p. 102. The Library forms used here are
`quaternionicProperWittSplit` (split case, rank at least two) and
`exists_properIsometry_skewGram_division` (division case).
