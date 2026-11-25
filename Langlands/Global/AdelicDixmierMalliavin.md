# The Dixmier–Malliavin theorem for adelic test functions

`Langlands.Global.AdelicDixmierMalliavin`. One theorem, in the Library's notion of test function on
the adelic points of a reductive group.

## Statement

`Langlands.Global.AdelicGroupPoints.IsAdelicTestFunction.exists_eq_sum_convolution`: let `F` be a
number field and `G` a group scheme over `F` with `[IsAffine G.X.left]`,
`[LocallyOfFiniteType G.X.hom]` and `hG : IsConnectedReductive G`. For every
`f : AdelicGroupPoints F G → ℂ` with `IsAdelicTestFunction F G f` there are `n` and
`φ ψ : Fin n → C_c(AdelicGroupPoints F G, ℂ)` such that every `φ i` and `ψ i` is again a test function
and

`f g = ∑ i, ∫ a, φ i a * ψ i (a⁻¹ * g) ∂Measure.haar` for all `g`,

for the Haar measure `Measure.haar` of `G(𝔸_F)` (with the Borel structure of
`Langlands/Global/AdelicGroupHaarMeasure`). The two instance hypotheses are needed for the statement
to make sense (`IsAdelicTestFunction` and the local compactness behind `Measure.haar`); the second
follows from `hG`.

## Proof

Through `AdelicGroupPoints.split : G(𝔸_F) ≃ₜ* G(F_∞) × G(𝔸_f)`, `f` becomes a compactly supported
continuous function `f'` on the product whose slices `a ↦ f'(a, b)` are the Library's infinite
slices, smooth for the reductive atlas by `reductive_isPlotSmooth_iff_contMDiff`. The right
invariance group `L` of `f` is intersected with `FiniteAdelicGroupPoints.compactOpenSubgroup`, giving
a compact open `V`. With the closed linear realization of `G(F_∞)` of
`Langlands/Global/InfiniteAdelicLinearRealization`, the theorem on products
(`Langlands.Analysis.DixmierMalliavin.exists_eq_sum_convolutionIntegral_prod`) applies to `f'` and the
image of `Measure.haar` (a Haar measure on the product). Its factors are transported back: they are
continuous with compact support, their infinite slices are smooth, they are right invariant under
`V`, and left invariant under an open subgroup (`bVb⁻¹` or `V`), which are the clauses of
`IsAdelicTestFunction`. The convolutions are transported by
`Langlands.Hecke.convolutionIntegral_comp_continuousMulEquiv`.

## Literature

The factorization of smooth compactly supported functions on adelic groups into convolutions is
the form of Dixmier–Malliavin used, for instance, in J. R. Getz and H. Hahn, *An introduction to
automorphic representations* (see `Langlands/Analysis/BoundedContinuousSmoothingStatement`, which
cites their Theorem 4.2.9).
