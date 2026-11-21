# Harish-Chandra decomposition of weighted `L²` by constant-term operators

Module `Langlands.Global.AdelicL2HarishChandraDecomposition`. Main result:
`Langlands.Global.StandardParabolicFamily.exists_componentOperators`. Its statement form is
`Langlands.Global.L2HarishChandraDecompositionStatement`, proved by
`Langlands.Global.l2HarishChandraDecomposition`.

## Statement

Let `𝓕 : StandardParabolicFamily F G` be a compatible standard parabolic family of a connected
reductive group over a number field `F`, in an arbitrary universe `u`. Let
`Λ₀ = StandardConstantTerm.minimalParabolicImage F G 𝓕.i 𝓕.ν` be the image of `P₀(F)` in `G(𝔸)`,
and `D₀` the Library's Borel fundamental domain of `Λ₀` in `G(𝔸)`. Let
`W : G(𝔸) → [0, ∞]` be measurable and left-invariant under `Λ₀` and under every standard
unipotent group `U_J(𝔸)`, `J ⊆ Δ₀`. Put `μ_W = weightedHaar W = (Haar|_{D₀}).withDensity W`.
Then there are continuous linear maps `T S` of `L²(μ_W)`, one for each finset `S` of characters,
such that:

1. `‖T S‖ ≤ 1` for every `S`.
2. For every `Fn ∈ L²(μ_W)` and every measurable representative `f`, `T S Fn` is `μ_W`-a.e. the
   folded constant term of `f` along `U_{S ∩ Δ₀}`. This is
   `foldConstantTerm Λ₀ D₀ hD₀ (U(𝔸) ↪ G(𝔸)) haar C f` with `U = standardUnipotent 𝓕.i 𝓕.ν (S ∩ Δ₀)`
   and `C` the Borel fundamental domain of `U(F)` in `U(𝔸)`.
3. `Σ_{P ⊆ Δ₀} Σ_{S ⊆ P} (−1)^{|P ∖ S|} T S = id`.
4. `‖Σ_{S ⊆ P} (−1)^{|P ∖ S|} T S‖ ≤ 2^{|P|}` for every `P`.

By `Langlands.Global.AdelicFoldConstantTermBridge`, the folded constant term in item 2 equals the
Library constant term `𝓕.constantTerm` on measurable `Λ₀`-invariant functions.

## Proof

- `HarishChandraDecomposition.norm_alternatingSum_le`: an alternating sum of contractions over the
  `2^{|P|}` subsets of `P` has norm at most `2^{|P|}` (triangle inequality,
  `‖(−1)^k‖ = 1`, `Finset.card_powerset`).
- `HarishChandraDecomposition.norm_le_sum_norm_alternatingSum`: if `T D = id`, then
  `‖x‖ ≤ Σ_{P ⊆ D} ‖(alternating sum over P) x‖`. This follows from the Möbius identity
  `sum_alternatingSum` of `Langlands.Global.AdelicHarishChandraDecomposition`, applied in the
  complex vector space of operators.
- `coe_eq_one_of_mem_top`: the adelic points of `U_{Δ₀}` are trivial, because
  `standardUnipotent_simple_eq_bot` holds and `Δ₀ ∩ Δ₀ = Δ₀`.
- `foldConstantTerm_top_of_mem`: for `g ∈ D₀`, the folded constant term along `U_{Δ₀}` of any `f`
  is `f g`. The integrand is constant, `C` has finite positive Haar measure, and `fold g = g` on
  `D₀`.
- `exists_componentOperators`: `T S` is chosen from
  `StandardConstantTerm.standardConstantTermOperator` (module
  `Langlands.Global.AdelicStandardConstantTermOperator`) for `J = S ∩ Δ₀`. Since `μ_W` is carried by
  `D₀`, the previous item gives `T Δ₀ Fn = Fn` almost everywhere, hence `T Δ₀ = id`.
- `l2HarishChandraDecomposition` combines these with `sum_alternatingSum`.

## Provenance

Joseph Bernstein and Erez Lapid, *On the meromorphic continuation of Eisenstein series*,
J. Amer. Math. Soc. 37 (2024), 187–234, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, §7.3 (pp. 214–215). They state the
decomposition into cuspidal parts with projections `Σ_{Q ⊆ P} (−1)^{dim 𝔞_Q^P} CT_Q` and use it on
weighted `L²` spaces whose weight factors through the height. This module proves the parts of the
decomposition that do not need orthogonality, on the weighted `L²` space of a fundamental domain of
`P₀(F)`: the components sum to the identity and are bounded by `2^{|P|}`. It does not prove that the
components are orthogonal or idempotent. It does not prove their cuspidality in `L²`; cuspidality
is proved pointwise for continuous automorphic inputs in `AdelicHarishChandraDecomposition`.
