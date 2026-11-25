# Series of directional derivatives on a linear Lie group

`Langlands.Analysis.DixmierMalliavin.DirectionalSeries`. For `h : IsExpLieAlgebra G 𝔤` (see
`Langlands/Geometry/Manifold/LinearLieGroup/Basic`), `X ∈ 𝔤` and `f : G → ℂ`, the derivatives of `f`
along the one-parameter subgroup `t ↦ exp (t X)` acting on the left, and the series of such
derivatives that the Dixmier–Malliavin theorem uses. The declarations are in the namespace
`Langlands.LinearLieGroup.IsExpLieAlgebra`, except the analysis lemma `contDiff_iteratedDeriv_snd`
in `Langlands.Analysis.DixmierMalliavin`.

## Content

- `dirDeriv X p f x = (d/dt)^p f (exp (t X) x)|_{t=0}`; by the one-parameter group law,
  `(d/dt)^p f (exp (t X) x)|_{t=s} = dirDeriv X p f (exp (s X) x)` (`iteratedDeriv_comp_expG_mul`).
- For smooth `f` (for the exponential charts): `t ↦ f (exp (t X) x)` is smooth, `dirDeriv X p f` is
  smooth (`contDiff_dirDeriv_mul_expG`, through `contDiff_iteratedDeriv_snd` applied to
  `(Y, t) ↦ f (exp (t X) g exp Y)`), and it vanishes outside the support of `f`
  (`dirDeriv_eq_zero_of_notMem`).
- `exists_bound_dirDeriv`: for smooth compactly supported `f` there is `M : ℕ → ℝ` with
  `‖dirDeriv X p f x‖ ≤ M p` for all `p`, `x`, such that whenever `∑ |c p| M p < ∞` the function
  `x ↦ ∑' p, c p * dirDeriv X p f x` is smooth and compactly supported. The support of `f` is covered
  by finitely many sets `{x : ‖chart g x‖ < 1}`; in the chart at `g`, `dirDeriv X p f` is cut off by a
  bump function equal to `1` on the unit ball, and `M p` is the sum over these `g` of the sup norms of
  the derivatives of order `k ≤ p` of the cut-off function. In every chart the `k`-th derivatives of
  the terms with `p ≥ k` are then bounded by `|c p| M p`, so the series of `k`-th derivatives
  converges uniformly (`contDiff_tsum`).

The sequence `M` is the one fed to the one-variable lemma
`Langlands.Analysis.DixmierMalliavin.exists_dirac_eq_tsum_iteratedDeriv_add` in `LinearGroup`.

## Literature

J. Dixmier and P. Malliavin, *Factorisations de fonctions et de vecteurs indéfiniment
différentiables*, Bull. Sci. Math. (2) 102 (1978), §3, proof of Theorem 3.1, step (2), p. 7: the
bounds (9) and the condition (10) make the series `∑ (-1)ⁿ αₙ x₁^{2n} ∗ φ` converge in `𝒟(G)`. The
page is that of the English translation *Factorizations of infinitely differentiable functions and
smooth vectors* (typeset in LaTeX, translator not named, paginated 1–24), which does not give the
pages of the original. Dixmier and Malliavin work on any Lie group, take only the even orders `2n`,
and bound the operators `uᵢ ∗ x₁^{2n}` for a basis `(uᵢ)` of the enveloping algebra `U(𝔤)`.

## Source and licence

Port of `src/GroundTheory/AutomorphicForms/DixmierMalliavinSeries.lean`, lines 10–200 (all
declarations), of the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>) at commit
`f1f6d65420dbbf36d6cfdac1af8d79511a855a5b`. The repository has no licence file; its text is used
with attribution (see `licenses/RiemannHypothesis/SOURCE.md`).

Changes against the source:

- Namespace `GroundTheory.Automorphic` becomes `Langlands.LinearLieGroup` for the group lemmas and
  `Langlands.Analysis.DixmierMalliavin` for `contDiff_iteratedDeriv_snd` (which the source has at the
  root of its namespace).
- The imports of `GKModules.SmoothVectors` (for `expG_zero`, `contMDiff_expG_comp`, now in `Basic`)
  and of `DixmierMalliavinBasic` are replaced by `Langlands.Geometry.Manifold.LinearLieGroup.Basic`
  and the Mathlib modules used.
- Unused section instances are left out with `omit … in`.
- A module docstring and a docstring for every declaration are added.
- Statements and proofs are otherwise unchanged.
