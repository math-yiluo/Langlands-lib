# Elements of a coalgebra shifted under a coefficient map

Author: Worker 1502. Internal helper for the proof of
`AffineHomogeneousQuotientReductiveStatement`. It is derived from the Library's coalgebra
translation operators (`AffineLinearEmbedding.rightAct`, `leftAct`, `Chevalley.regularSpan`,
`Chevalley.subspaceMatrix`) and does not follow a cited source.

Namespace `Langlands.GroupScheme.AdditiveShift`. `K` is a field. `B` is a commutative `K`-algebra
with a `K`-coalgebra structure `Δ, ε`. `φ : B →ₐ[K] C` is an algebra map to a commutative
`K`-algebra `C`, and `ψ : C`. For `B` the coordinate ring of a group `G` and `φ` restriction to a
subgroup `N`, the identities below say `u(n x) = u(x) + a ψ(n)`.

- `comul_rightAct`: `Δ (rightAct f u) = (id ⊗ rightAct f) (Δ u)`, by coassociativity.
- `IsShift φ ψ u a` is the identity `(φ ⊗ id)(Δ u) = 1 ⊗ u + a • (ψ ⊗ 1)` in `C ⊗[K] B`.
- `IsShift.map_eq`: if `ε 1 = 1`, then `IsShift φ ψ u a` gives `φ u = ε(u) • 1 + a • ψ`. Apply
  `id ⊗ ε` and use the counit law.
- `IsShift.rightAct`: if `Δ 1 = 1 ⊗ 1`, then `IsShift φ ψ u a` gives
  `IsShift φ ψ (rightAct f u) (a * f 1)` for every functional `f`. Use `comul_rightAct` and
  `rightAct f 1 = f 1 • 1`.
- `shiftSubmodule φ ψ` is the subspace of all `u` with `IsShift φ ψ u a` for some `a`.
  `regularSpan_le_shiftSubmodule`: if `IsShift φ ψ h 1`, the span of all right translates of `h`
  lies in it.
- `shiftCoeff φ lam = lam ∘ φ - lam(1) • ε`, for a functional `lam` on `C`.
  `IsShift.eq_shiftCoeff`: if `lam ψ = 1`, the shift coefficient `a` equals `shiftCoeff φ lam u`.
  So the coefficient is unique and depends linearly on `u`.
- `basis_eq_sum_counit`: for a basis `b` of a right-translation-stable finite-dimensional
  subspace `V`, with Library coefficients `M = subspaceMatrix V b`,
  `b j = ∑ i, ε(b i) • M i j`. Apply `ε ⊗ id` to `Chevalley.comul_basis`.
- `sum_shiftCoeff_smul_subspaceMatrix`: if moreover `V ≤ shiftSubmodule φ ψ`, `ε 1 = 1` and
  `lam ψ = 1`, then `∑ i, ℓ i • M i j = ℓ j • 1`, where `ℓ i = shiftCoeff φ lam (b i)`. The left
  translate `leftAct (lam ∘ φ) (b j)` is computed in two ways: from `comul_basis` it is
  `∑ i, lam(φ(b i)) • M i j`; from the shift identity it is `lam(1) • b j + ℓ j • 1`. Then
  `lam(φ(b i)) = ε(b i) lam(1) + ℓ i` and `basis_eq_sum_counit` cancel the `lam(1)` terms.
