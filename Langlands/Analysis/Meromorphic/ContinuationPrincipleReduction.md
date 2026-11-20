# The principle of meromorphic continuation, from Hartogs's theorem

Module `Langlands.Analysis.Meromorphic.ContinuationPrincipleReduction` proves
the openness in part (1) and parts (2) and (3) of Bernstein–Lapid's Theorem 3.3
(the principle of meromorphic continuation). It assumes Hartogs's theorem on
separate holomorphy, in the diagonal form `HartogsDiagonal E` of
`Langlands.Analysis.Meromorphic.WeakComposition`, as its one named premise.
The main result is `meromorphicContinuationHolomorphic_of_hartogs`. If
`HartogsDiagonal E` holds for every finite-dimensional complex normed space `E`
in universe `uE`, then
`Langlands.Analysis.Meromorphic.MeromorphicContinuationHolomorphicStatement.{uE, uM, uV, uι, uF}`
holds. That statement is not proved outright here, because Hartogs's theorem
is not proved here. The analyticity of the complement of `M_unq` in part (1)
is neither proved nor used.

## Source

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`. The relevant parts
are:

- Theorem 3.3, p.194 (TeX `1911.02342.tex` lines 716–740).
- Its proof in Appendix A, pp.230–231 (TeX lines 3817–3990), using Cramer's
  rule.
- The remark in §3.2, p.193 (TeX lines 665–669), that composites of analytic
  families are analytic by Hartogs's theorem.

The Lean proof follows Appendix A. It differs in three places:

- The local denominator and numerator are a determinant and an adjugate
  solution, so no division occurs.
- The identity `f · v = u` on `M_unq` is purely algebraic.
- The global step is the clopen argument for the closure of the interior of
  `M_unq`, described below.

## Ingredients

- `Langlands.Analysis.Meromorphic.ManifoldIdentity`: separation by continuous
  complex linear forms (`eq_of_forall_clm_apply_eq`), chart balls
  (`ChartBall`, `exists_chartBall_subset`), and the identity theorem on chart
  balls (`ChartBall.eqOn_zero`).
- `Langlands.Analysis.Meromorphic.WeakComposition`: the premise
  `HartogsDiagonal E` and the holomorphy of `s ↦ φ (μ s (w s))`.
- `Langlands.Analysis.Meromorphic.LocalScalarization`: for a choice
  `a : Fin n → Σ i, (F i →L[ℂ] ℂ)` of `n` scalar equations, the matrix
  `A = scalarMatrix μ ℓ a` and the adjugate solution
  `u = adjugateSolution μ c ℓ a`. It provides Cramer's rule
  `det A(s) • x = u s` (`det_smul_eq_adjugateSolution`), the holomorphy of
  `det A`, of `u` and of the residuals, and `exists_det_scalarMatrix_ne_zero`.

Notation and standing hypotheses. `E` is a complex normed space and `M` a
manifold charted on `E` with `IsManifold 𝓘(ℂ, E) 1 M`. `V` is a complex vector
space with a topology. The `F i` are complex, Hausdorff and locally convex, as
in the target statement. `(μ, c)` is an analytic system (`hsys`),
`P = uniqueSolutionLocus μ c` (the set `M_unq`), and `Sol s = systemSolutions μ c s`.

## Local frames: `exists_chartBall_frame`

If a family `A : M → Set V` is of locally finite type, every `s₀` has a chart
ball `W ∋ s₀` and `ℓ : M → (ℂⁿ →L[ℂ] V)` with the following properties: `ℓ` is a
holomorphic family on `W`, `ℓ s` is injective for `s ∈ W`, and `A s ⊆ range (ℓ s)`
for `s ∈ W`. One takes the finite-type neighbourhood and a chart ball inside it
(`exists_chartBall_subset`).

## The local claim: `systemSolutions_eq_of_det_ne_zero`

Let `hH : HartogsDiagonal E`. Let `W` be a chart ball with a frame `ℓ` that is
holomorphic on `W` and whose ranges contain the solution sets, and suppose `W`
meets `interior P`. Then for every choice `a` and every `s ∈ W` with
`det A(s) ≠ 0`, `Sol s = {(det A(s))⁻¹ • u s}`.

Proof. For each `i` and each continuous linear form `φ` on `F i`, the residual
`φ (μ i s (u s)) - det A(s) * φ (c i s)` is holomorphic on `W`. It vanishes on
the nonempty open set `W ∩ interior P`. There a solution `w` exists, and
Cramer's rule gives `u s = det A(s) • w`, so
`φ (μ i s (u s)) = det A(s) * φ (c i s)`. By the identity theorem on the chart
ball it vanishes on all of `W`. So if `det A(s) ≠ 0`, each
`φ (μ i s ((det A(s))⁻¹ • u s))` equals `φ (c i s)`, and `(det A(s))⁻¹ • u s` is a
solution by separation in `F i`. Every solution `x` satisfies
`det A(s) • x = u s`, so it is the only one.

`mem_uniqueSolutionLocus_iff_exists_det_ne_zero`: assume in addition that each
`ℓ s` (`s ∈ W`) is injective. Then for `s ∈ W`, `s ∈ P` holds if and only if
`det (scalarMatrix μ ℓ a s) ≠ 0` for some `a : Fin n → Σ i, (F i →L[ℂ] ℂ)`.
"Only if" is `exists_det_scalarMatrix_ne_zero`, and "if" is the local claim.

## The global step: `closure_interior_uniqueSolutionLocus_eq_univ`

Let `M` be connected, with `hH`, `hsys`, `hft` (locally finite type of the
solution sets) and `interior P` nonempty. Then `closure (interior P) = M`.

The closure is closed and nonempty, so it suffices that it is open. Let `s₀` be
in it, take a frame `W, ℓ` at `s₀`, and pick `s₁ ∈ W ∩ interior P`. Choose `a`
with `f = det A` nonzero at `s₁`. By the local claim, the open set
`W ∩ f⁻¹({0}ᶜ)` lies in `P`, hence in `interior P`. Now let `x ∈ W` and `O ∋ x` be
open. If `O` missed `interior P`, then `f` would vanish on `O ∩ W`, hence on
`W` by the identity theorem, contradicting `f s₁ ≠ 0`. So
`W ⊆ closure (interior P)`.

`exists_local_data` (with `M` connected, `hH`, `hsys`, `hft` and
`interior P ≠ ∅`): every `s₀` has a chart ball `W ∋ s₀` with the following
property. For every `s₁ ∈ W ∩ P` there are `f` and `u`, holomorphic on `W`,
with `f s₁ ≠ 0`, `f s • x = u s` for `s ∈ W` and `x ∈ Sol s`, and
`Sol s = {(f s)⁻¹ • u s}` wherever `f s ≠ 0`. Here `W` comes from
`exists_chartBall_frame`. It meets `interior P` by the global step. `f` and
`u` are `det A` and the adjugate solution for an `a` from
`exists_det_scalarMatrix_ne_zero` at `s₁`.

## The conclusion: `exists_holomorphic_meromorphic_of_hartogs`

Same hypotheses as `exists_local_data`.

1. `P` is open. For `s₁ ∈ P`, take `W`, `f` and `u` from `exists_local_data`.
   Then `W ∩ f⁻¹({0}ᶜ)` is an open neighbourhood of `s₁` contained in `P`.
2. `v s` is the chosen unique solution for `s ∈ P` (and `0` elsewhere), so
   `Sol s = {v s}` on `P`.
3. `v` is holomorphic on `P`. Near `s₁ ∈ P`, on `W ∩ f⁻¹({0}ᶜ)`, one has
   `v s = (f s)⁻¹ • u s`. So `φ (v s) = (f s)⁻¹ * φ (u s)`, which is
   holomorphic.
4. `v` is meromorphic on `P` (`IsMeromorphicOn`). `P` is open and dense,
   because it contains the dense set `interior P`, and `v` is holomorphic on
   it. For any `s₀`, take its chart ball `W`. It is open and connected
   (nonempty and preconnected). Pick `s₁ ∈ W ∩ interior P` and the local `f`
   and `u`. Then `g = f` is holomorphic on `W` and nonzero at `s₁`, `h = u` is
   holomorphic on `W`, and `f s • v s = u s` for `s ∈ P ∩ W` because `v s` is a
   solution.

`meromorphicContinuationHolomorphic_of_hartogs` unfolds
`MeromorphicContinuationHolomorphicStatement`, introduces its data and applies
`exists_holomorphic_meromorphic_of_hartogs` with the premise for the given `E`.
It uses only the hypotheses of the statement. The hypotheses that `V` is
locally convex and Hausdorff are not needed: separation is used only in the
spaces `F i`. Finite dimensionality of `E` is used only through the premise.
