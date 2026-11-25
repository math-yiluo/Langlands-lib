# The Dixmier–Malliavin theorem on linear Lie groups

`Langlands.Analysis.DixmierMalliavin.LinearGroup`. The theorem of Dixmier and Malliavin for a Lie
subgroup `G` of the units of a finite-dimensional normed real algebra `𝔸`, given by
`h : IsExpLieAlgebra G 𝔤` and carrying its exponential charts (`letI := h.chartedSpace`). Namespace
`Langlands.LinearLieGroup.IsExpLieAlgebra`.

## Statements

- `exists_eq_sum_convolutionIntegral`: let `μ` be a left Haar measure on `G`, `U` a neighbourhood of
  `1`, and `f : G → ℂ` smooth with compact support. Then there are `n` and `φ ψ : Fin n → G → ℂ` with
  every `φ i` smooth, compactly supported, `tsupport (φ i) ⊆ U`, every `ψ i` smooth with
  `tsupport (ψ i) ⊆ tsupport f`, and
  `f = ∑ i, Langlands.Hecke.convolutionIntegral μ (φ i) (ψ i)`, that is
  `f x = ∑ᵢ ∫ φᵢ(y) ψᵢ(y⁻¹ x) dμ(y)`.
- `exists_eq_sum_integral_revProdExp`: for `ε > 0`, any `X : Fin d → 𝔤` and smooth compactly
  supported `f`, there are smooth `Fᵢ` with `tsupport Fᵢ ⊆ tsupport f` and smooth kernels `Kᵢ` on
  `ℝ^d` supported in the closed `ε`-ball with
  `f x = ∑ᵢ ∫ Kᵢ(t) Fᵢ(exp (t_{d-1} X_{d-1}) ⋯ exp (t₀ X₀) · x) dt` for all `x`.
- `exists_eq_integral_add_integral_direction`: the case of one direction, with `[0, ε]`-supported
  kernels on `ℝ`: `f x = ∫ g(t) f₁(exp (t X) x) dt + ∫ k(t) f(exp (t X) x) dt` with
  `f₁ = ∑ c_p dirDeriv X p f`.

## Proof

*One direction.* `exists_bound_dirDeriv` (`DirectionalSeries`) gives `M` with
`‖dirDeriv X p f‖ ≤ M p` such that every series `∑ c_p dirDeriv X p f` with `∑ |c_p| M_p < ∞` is smooth
and compactly supported. The one-variable lemma with this `M` gives `c`, `g`, `k`; applied to
`F(t) = f (exp (t X) x)`, whose derivatives are `dirDeriv X p f (exp (t X) x)`, it gives
`f(x) = ∑ c_p ∫ dirDeriv X p f (exp (t X) x) g(t) dt + ∫ f(exp (t X) x) k(t) dt`, and the sum and the
integral are exchanged (absolute convergence).

*A basis.* By induction on `d`: decompose `f` in the direction `X₀`, then expand both `f₁` and `f`
over the remaining directions and combine with `sum_integral_cons_kernel` (`IteratedKernel`). The
kernels of `f₁` are multiplied by `g(t₀)`, those of `f` by `k(t₀)`.

*Convolutions.* For a basis `b` of `𝔤` and `ε` small, `exists_smooth_density_prodExp`
(`Langlands/Geometry/Manifold/LinearLieGroup/HaarDensity`) gives smooth compactly supported `κᵢ` on
`G`, supported in the image of the `ε`-ball under the coordinates of the second kind, with
`∫ κᵢ φ dμ = ∫ Kᵢ(-t) φ(prodExp b t) dt`. With `φ = Fᵢ(·⁻¹ x)` and `(revProdExp b t)⁻¹ = prodExp b (-t)`,
the `i`-th average is `(κᵢ ⋆ Fᵢ)(x)`. Choosing `ε` so that the image of the ball lies in `U` gives the
support condition on `φᵢ = κᵢ`; `ψᵢ = Fᵢ`.

## Literature

J. Dixmier and P. Malliavin, *Factorisations de fonctions et de vecteurs indéfiniment
différentiables*, Bull. Sci. Math. (2) 102 (1978), §3, Théorème 3.1; page 6 of the English
translation *Factorizations of infinitely differentiable functions and smooth vectors* (translator
not named, with its own page numbers), where it is Theorem 3.1, proved on pages 6–7 (the
coordinates of the second kind in step (1), page 6). The theorem there is stated for every real Lie
group; here `G` is a Lie subgroup of the units of a finite-dimensional normed real algebra.

## Source and licence

Port of `src/CompanionTheory/AutomorphicTheory/PadicUnitaryWeights/DixmierMalliavin/DecompDirection.lean`,
lines 9–110 and 188–230, of the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>) at commit
`f1f6d65420dbbf36d6cfdac1af8d79511a855a5b` (lines 112–186 of that file are in `HaarDensity`). The
file replaces the source's `src/GroundTheory/AutomorphicForms/DixmierMalliavin.lean`, which proves
the same three steps without the support clauses. The repository has no licence file; its text is
used with attribution (see `licenses/RiemannHypothesis/SOURCE.md`).

Changes against the source:

- Namespace `CompanionTheory.DM` becomes `Langlands.LinearLieGroup.IsExpLieAlgebra`.
- Names: `decomp_direction` → `exists_eq_integral_add_integral_direction`, `decomp_iter` →
  `exists_eq_sum_integral_revProdExp`, `factor` → `exists_eq_sum_convolutionIntegral`.
- The source's convolution `groupConv` (of its file `HeckeAlgebra`) is replaced by the Library's
  `Langlands.Hecke.convolutionIntegral` (same integral).
- `exists_eq_sum_convolutionIntegral`: the neighbourhood is called `U`, and the conjuncts are in the
  order smooth `φ i`, compact support of `φ i`, `tsupport (φ i) ⊆ U`, smooth `ψ i`,
  `tsupport (ψ i) ⊆ tsupport f` (the source puts the smoothness of `ψ i` before the support of `φ i`).
- `exists_eq_integral_add_integral_direction` gives kernels supported in `[0, ε]` (source:
  `[-ε, ε]`), as the one-variable lemma now does; the induction step weakens this to `[-ε, ε]` for
  `tsupport_cons_kernel`.
- `import` lines are replaced by the Library modules and the Mathlib modules used.
- A module docstring and a docstring for every declaration are added.
- Proofs are otherwise unchanged.
