# Iterating the one-direction decomposition over a basis

`Langlands.Analysis.DixmierMalliavin.IteratedKernel`. Product kernels on `ℝ^{d+1}`, Fubini over
`ℝ × ℝ^d`, and the reversed products of exponentials in which the Dixmier–Malliavin decomposition
is written. The analysis lemmas are in the namespace `Langlands.Analysis.DixmierMalliavin`, the group
lemmas in `Langlands.LinearLieGroup.IsExpLieAlgebra`.

## Content

- `integral_fin_succ_cons`: `∫ F = ∫ (∫ F (Fin.cons s t') dt') ds` on `ℝ^{d+1}` for integrable `F`
  (Mathlib's measure-preserving `MeasurableEquiv.piFinSuccAbove` and `integral_prod`).
- `contDiff_cons_kernel`, `tsupport_cons_kernel`: for smooth `a` on `ℝ` supported in `[-ε, ε]` and
  smooth `K` on `ℝ^d` supported in the closed `ε`-ball, `t ↦ a(t₀) K(tail t)` is smooth and supported
  in the closed `ε`-ball of `ℝ^{d+1}` (sup norm).
- `IsExpLieAlgebra.revProdExp X t = exp (t_{d-1} X_{d-1}) ⋯ exp (t₀ X₀)` (the product of
  `Basic.prodExp` in the reverse order): `revProdExp X t = revProdExp (tail X) (tail t) · exp (t₀ X₀)`,
  it is continuous, and `(revProdExp X t)⁻¹ = prodExp X (-t)` (`revProdExp_inv`).
- `IsExpLieAlgebra.sum_integral_cons_kernel`: if `f₁ y = ∑ᵢ ∫ Kᵢ(t') Fᵢ(revProdExp (tail X) t' · y) dt'`
  for all `y`, then
  `∑ᵢ ∫ a(t₀) Kᵢ(tail t) Fᵢ(revProdExp X t · x) dt = ∫ a(s) f₁(exp (s X₀) x) ds`.
  By Fubini (`integral_cons_kernel`), the first coordinate of `t` separates as the left translation
  by `exp (s X₀)`.

This is the induction step of `IsExpLieAlgebra.exists_eq_sum_integral_revProdExp` in `LinearGroup`.

## Literature

J. Dixmier and P. Malliavin, *Factorisations de fonctions et de vecteurs indéfiniment
différentiables*, Bull. Sci. Math. (2) 102 (1978), §3, proof of Theorem 3.1, steps (1) and (3),
pp. 6–7: the map `ζ(t₁, …, t_m) = (exp t₁x₁) ⋯ (exp t_m x_m)` and the induction over the basis, in
which `ξ₁ ∗ ⋯ ∗ ξ_m` is the image under `ζ` of `f₁(t₁) ⋯ f_m(t_m) dt₁ ⋯ dt_m`. The pages are those of
the English translation *Factorizations of infinitely differentiable functions and smooth vectors*
(typeset in LaTeX, translator not named, paginated 1–24), which does not give the pages of the
original.

## Source and licence

Port of `src/GroundTheory/AutomorphicForms/DixmierMalliavinProducts.lean`, lines 12–147 (all
declarations), of the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>) at commit
`f1f6d65420dbbf36d6cfdac1af8d79511a855a5b`. The repository has no licence file; its text is used
with attribution (see `licenses/RiemannHypothesis/SOURCE.md`).

Changes against the source:

- Namespace `GroundTheory.Automorphic` becomes `Langlands.Analysis.DixmierMalliavin` for
  `integral_fin_succ_cons`, `contDiff_cons_kernel`, `tsupport_cons_kernel` (root-level names of the
  source namespace) and `Langlands.LinearLieGroup` for the rest.
- `contDiff_apply ℝ ℝ i` is written `contDiff_apply ℝ (fun _ => ℝ) i` (changed signature in the
  present Mathlib).
- The file option `linter.unusedSectionVars false` is removed; unused section instances are left
  out with `omit … in`.
- `import Mathlib` and the project imports are replaced by `Langlands.Geometry.Manifold.LinearLieGroup.Basic`
  and the Mathlib modules used.
- A module docstring and a docstring for every declaration are added.
- Statements and proofs are otherwise unchanged.
