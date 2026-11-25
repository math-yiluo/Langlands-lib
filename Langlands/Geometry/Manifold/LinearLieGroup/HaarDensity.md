# The Haar measure of a linear Lie group in coordinates of the second kind

`Langlands.Geometry.Manifold.LinearLieGroup.HaarDensity`. For `h : IsExpLieAlgebra G 𝔤`, a basis
`b` of `𝔤` indexed by `Fin d`, and a left Haar measure `μ` on `G`, the Haar measure near `1` in the
coordinates of the second kind `P(z) = h.prodExp b z = ∏ᵢ exp (zᵢ bᵢ)` has a smooth positive density.
Namespace `Langlands.LinearLieGroup`.

## Statements

- `IsExpLieAlgebra.exists_haar_density_prodExp`: there are `r > 0`, a smooth `ρ : ℝᵈ → ℝ` positive
  on the ball `B(0, r)`, an open `W ⊆ G` and `c : G → ℝᵈ` with `P(B(0, r)) ⊆ W`, `c ∘ P = id` on the
  ball, `P ∘ c = id` on `W`, `Y ↦ c (g exp Y)` smooth at `0` for `g ∈ W`, and
  `∫ ψ dμ = ∫_{B(0, r)} ψ(P z) ρ(z) dz` for every continuous compactly supported `ψ` with
  `tsupport ψ ⊆ P(B(0, r))`.
- `IsExpLieAlgebra.exists_smooth_density_prodExp`: there is `ε > 0` such that for `δ ≤ ε` every
  smooth `K : ℝᵈ → ℂ` supported in `B̄(0, δ)` is `∫ K(t) φ(P t) dt = ∫ κ φ dμ` for a smooth compactly
  supported `κ` on `G` (for the exponential charts) with `tsupport κ ⊆ P(B̄(0, δ))`. One takes
  `κ = (K / ρ) ∘ c` on `W` and `0` outside.
- `contDiffOn_det_fderiv_snd`: for `Λ : E × ℝᵈ → ℝᵈ` smooth on an open set `O`, the Jacobian
  `q ↦ det (∂₂Λ(q))` is smooth on `O`.
- `integral_mul_integral_eq_setIntegral_of_forall`: on a locally compact second countable group
  with left Haar measure `μ`, for continuous `P : ℝᵈ → G` and continuous compactly supported `β`,
  `Θ`, `ψ`: if `∫ β(t) ψ(P t · x) dt = ∫_s ψ(P z) Θ(x, z) dz` for every `x`, then
  `(∫ β) ∫ ψ dμ = ∫_s ψ(P z) (∫ Θ(x, z) dμ(x)) dz` (Fubini twice and left invariance).

## Proof of the density

Let `ψ` be the local inverse of the transition map of `ProductCoordinates`, and
`Λ(a, z) = ψ (logCoord b (p(z) a))` for `a ∈ 𝔸` near `1` (`p = prodExpVal`): `P(Λ(x⁻¹, z)) = P(z) x⁻¹`.
Let `J(a, z) = det ∂_zΛ(a, z)`; it is smooth (`contDiffOn_det_fderiv_snd`), `J(1, z) = 1`, and by a
tube lemma it is positive for `a` near `1` and `z` in a closed ball. With bump functions `θ` (in
`z`), `χ` (around `1 ∈ 𝔸`) and `β` (in `s`), put
`Ξ(a, z) = θ(z) χ(p(z) a) β(Λ(a, z)) J(a, z)`, smooth, nonnegative and compactly supported.

- For fixed `x`, the change of variables `s = Λ(x⁻¹, z)` (injective, Jacobian `J > 0`;
  `integral_image_eq_integral_abs_det_fderiv_smul`) gives
  `∫ β(s) ψ(P s · x) ds = ∫_{B(0, r)} ψ(P z) Ξ(x⁻¹, z) dz` for `ψ` supported in `P(B(0, r))`.
- By the averaging identity, `(∫ β) ∫ ψ dμ = ∫_{B(0, r)} ψ(P z) D(z) dz` with
  `D(z) = ∫ Ξ(x⁻¹, z) dμ(x)`.
- `D` is smooth: the integral is over a compact set of `x`, and the parameter integral of a smooth
  compactly supported function is smooth (`contDiff_integral_comp_of_hasCompactSupport`).
  `D(z) > 0` on the ball, because the integrand is nonnegative, continuous, and equal to `J(1, z)·1 > 0`
  at `x = P(z)`.

So `ρ = D / ∫ β`. The density is not computed explicitly; positivity and smoothness are all that
the Dixmier–Malliavin theorem needs.

## Literature

The density of Haar measure in canonical coordinates is classical (for instance J. Dixmier and
P. Malliavin, *Factorisations de fonctions et de vecteurs indéfiniment différentiables*, Bull. Sci.
Math. (2) 102 (1978), §3, proof of Theorem 3.1, step (3), p. 7: the image of `dt₁ ⋯ dt_m` on
`(-1, 1)^m` under `(t₁, …, t_m) ↦ (exp t₁x₁) ⋯ (exp t_m x_m)` is the left Haar measure times a
smooth function, stated without proof; the page is that of the English translation *Factorizations
of infinitely differentiable functions and smooth vectors*, typeset in LaTeX, translator not named,
paginated 1–24, which does not give the pages of the original). The averaging argument above is the
one of the Lean source.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>) at commit
`f1f6d65420dbbf36d6cfdac1af8d79511a855a5b`:

| Source (under `src/`) | Lines | Content here |
|---|---|---|
| `GroundTheory/AutomorphicForms/DixmierMalliavinHaar.lean` | 9–446 | `exists_haar_density_prodExp` |
| `GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean` | 258–320 | `contDiff_smul_of_tsupport`, `contDiff_integral_comp_of_hasCompactSupport` (private here) |
| `CompanionTheory/AutomorphicTheory/PadicUnitaryWeights/DixmierMalliavin/DecompDirection.lean` | 112–186 | `exists_smooth_density_prodExp` (source: `CompanionTheory.DM.smooth_density`) |

The repository has no licence file; its text is used with attribution (see `licenses/RiemannHypothesis/SOURCE.md`).

Changes against the source:

- Namespace `GroundTheory.Automorphic` (and `CompanionTheory.DM`) becomes `Langlands.LinearLieGroup`.
- The proof of `exists_haar_density_prodExp` is split: the smoothness of the Jacobian becomes the
  lemma `contDiffOn_det_fderiv_snd`, and the final double application of Fubini with left
  invariance becomes the lemma `integral_mul_integral_eq_setIntegral_of_forall`, stated for any
  locally compact second countable group; the main proof applies them (and proves the compact
  support of `(x, z) ↦ Ξ(x⁻¹, z)` that the second lemma asks for). The rest of the proof is the
  source text.
- The source's `contDiff_det_pi` is replaced by the Library's
  `Langlands.Analysis.contDiff_continuousLinearMap_det` (`Langlands/Analysis/SmoothLinearDeterminant.lean`).
- `smooth_density` is renamed `exists_smooth_density_prodExp` and sits in the namespace
  `IsExpLieAlgebra`; `h.secondCountableTopology` is replaced by `secondCountableTopology_subgroup G`.
- The exponential lemmas lose their field argument (see `Exponential`).
- `import Mathlib` is replaced by the modules the file uses.
- A module docstring and a docstring for every declaration are added.
