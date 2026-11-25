# Actual central convergence: proof of `RationalSchwartzCentralConvergenceStatement`

Module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSchwartzCentralConvergenceProof`,
namespace `Langlands.HarishChandraSchwartz`.

## Result

`Langlands.HarishChandraSchwartz.rationalSchwartzCentralConvergence :
RationalSchwartzCentralConvergenceStatement.{u}`

The statement and its correspondence with Waldspurger 2003 (VIII.4, the projections `p_χ`, and
III.6, the Schwartz space `C(G)`) are in `RationalCuspidalConvergenceStatements.md`. It says: for
a nonarchimedean local field `F`, a connected reductive `G` over `F` with maximal split torus `i`
and generic cocharacter `ν`, a compact open subgroup `K` of `G(F)` with `G(F) = P₀(F) K`, a
closed matrix representation `ρ`, a split component `s : T → G` with image `A_G(F)`, a Haar
measure `μ_A` on `A_G(F)` and a continuous unitary character `χ` of `A_G(F)`, every `f` in the
actual Schwartz space `RationalSchwartzSpace hKc hPK ρ` has absolutely convergent central
integrals `a ↦ χ(a)⁻¹ f(a g)` at every `g ∈ G(F)` (`CentralIntegralConvergesOn` on the whole
space `⊤`).

The theorem has no hypotheses. Its two inputs are published Library results imported by name.

## Proof

The theorem is `rationalSplitCenterHeight.schwartzCentralConvergence`, which applies two
published results:

1. `rationalSplitCenterHeight : RationalSplitCenterHeightStatement.{u}` (module
   `RationalSplitCenterHeightProof`) proves the height properties of the split centre `A_G(F)`;
2. `RationalSplitCenterHeightStatement.schwartzCentralConvergence :
   RationalSplitCenterHeightStatement.{u} → RationalSchwartzCentralConvergenceStatement.{u}`
   (module `RationalCuspidalConvergenceReductions`) is the reduction. Given all the data of the
   target, `RationalSplitCenterHeightStatement.centralWeights` (module `RationalCentralProjection`)
   turns the height statement into the actual `CentralWeights μ_A Ξ σ` for
   `Ξ = rationalXi hKc hPK` and `σ = rationalHeight ρ`. Then `CentralWeights.convergesOn` gives
   the convergence of the central integrals on every submodule of the Schwartz space for the
   unitary character `χ`, in particular on `⊤`.

## Remark: which part of the height statement is used

`RationalSplitCenterHeightStatement` has two clauses: (1) the comparison
`1 + σ(a) ≤ C (1 + σ(a g))` for `a ∈ A_G(F)`, `g ∈ G¹`, and (2) the integrability of
`(1 + σ(a))^{-r₀}` on `A_G(F)` for every Haar measure. Only clause 2 enters this proof:
`RationalSplitCenterHeightStatement.centralWeights` uses only the second component
(`(h F G hG T s hs N ρ hρ).2 muA`), which is the field `integrable` of `CentralWeights`. Clause 1
serves instead the rapid decay of `p_χ f` on `G¹`
(`RationalSplitCenterHeightStatement.exists_one_add_add_le` and
`RationalSplitCenterHeightStatement.enorm_rationalCentralProjection_le` in
`RationalCentralProjection`), which this theorem does not need.
