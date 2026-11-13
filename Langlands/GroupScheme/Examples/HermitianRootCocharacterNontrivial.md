# The diagonal cocharacter of the weighted Hermitian scheme is nontrivial

This module proves two facts about the published weighted Hermitian group
scheme `HermitianRoot.SchemeModel.groupScheme k L H w hw` (fields `k` and `L` in a
common universe, `L/k` separable quadratic, a diagonal Hermitian form `H` on a
finite middle index `Middle : Type` with unit weights `w`).

## `includeSections_injective`

For every test scheme `T` over `Spec k`, the inclusion
`SpecialLinear.WeilRoot.includeSections k L T` of the global sections
`Γ(T, O_T)` into the tensor coefficients `L ⊗[k] Γ(T, O_T)` is injective.

Proof: it is Mathlib's `Algebra.TensorProduct.includeRight`, which is
injective by `Algebra.TensorProduct.includeRight_injective` because `Γ(T, O_T)`
is flat over the field `k` and `algebraMap k L` is injective. (The two
hypotheses that `L/k` is quadratic and separable are omitted from this lemma.)

## `cocharacter_ne_zero`

If `k` is infinite, the published split diagonal cocharacter
`HermitianRoot.SchemeModel.cocharacter k L H w hw : Gm ⟶ groupScheme k L H w hw`
is not the zero (constant identity) homomorphism.

Proof, following the published
`FiniteAlgebraUnits.WeightedRoot.cocharacter_ne_zero_of_weight_eq_one`:

1. Since `k` is infinite, choose `c ∈ k` with `c ≠ 0` and `c ≠ 1`.
2. Let `T` be the affine test scheme `Spec k` over `Spec k`, with section
   algebra `R ≅ k` (`Corepresented.affineSectionsAlgEquiv`), and let `x` be the
   multiplicative point of `T` corresponding to the unit `c` of `R`
   (`Gm.pointsEquiv`).
3. If the cocharacter were zero, then `x ≫ cocharacter = 1`, so by
   `pointsEquiv_cocharacter_val` the matrix `diagonalMatrix (scalarUnit k L T x)`
   would be the identity matrix. Its entry at the first hyperbolic coordinate
   `(Sum.inl (), Sum.inl ())` is the scalar unit, so
   `includeSections k L T c = 1 = includeSections k L T 1`.
4. By `includeSections_injective`, `c = 1` in `R`; applying the algebra
   equivalence `R ≃ₐ[k] k` gives `c = 1` in `k`, a contradiction.

The provenance is internal: this is a computation with the published model and
its published cocharacter formula.
