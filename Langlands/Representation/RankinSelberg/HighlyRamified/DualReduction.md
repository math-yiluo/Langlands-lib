# Reduction of the dual corank-one integral to one rank lower

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`
(Jacquet–Shalika 1985, §4.4, passage from formula (3) to formula (9), printed
pages 327–328). The canonical topology, valuation and Borel structures of the p-adic field
are installed as local instances.

- `abv_eq_one_of_unit`: the normalized absolute value is `1` on integral units, from the
  published `normalizedAbs_le_one_iff_mem_integers`.
- `unitLowerSubgroup`: the open subgroup of integral units in the lower-triangular group of
  `GL_1` (preimage of the published `GeneralLinearGroup.integralSubgroup`);
  `mem_unitLowerSubgroup` describes membership by the entry and its inverse;
  `isCompact_unitLowerSubgroup`: it is compact, since the integer ring is compact and the
  lower-triangular subgroup is closed.
- `dualIntegrand_chart`: the dual corank-one integrand (`corankOneIntegrand` for `ψ⁻¹` of the
  first dual of the candidate test function and the second dual `f̃` of `f'`) at the chart point
  `[[[A,0],[x,c]]]` is `F̃(diag(h,1)) f̃(h) |det h|^(s-1/2)` with `h = [[A,0],[x,c]]`.
- `lastWeight χ S1 η c = S1(c) χ(det c)⁻¹ η(c)`.
- `dualIntegrand_chart_separated`: by `candidateTest_dual_lowerBlockPair` this value is
  `χ(det w) · lastWeight(c) · S2(rev x) χ(det A)⁻¹ f̃([[A,0],[x,1]]) |det A|^(s-1/2) W(M(diag(A,1)))`.
- `dual_integral_reduction ηH`: there is `C' > 0`, depending only on the rank and on the Haar
  measure `ηH`, such that for all such data with `lastWeight` equal to the indicator of
  `unitLowerSubgroup`, and for `s` at which the integrand is measurable and integrable,
  the dual corank-one integral equals
  `C' ∫ |det A|⁻¹ (∫ f(chart([A],x,1)) dx) dμ([A])` over `N_(m+1) \ GL_(m+1)`. The proof
  applies `integral_separate_last_iterated` with `κ = lastWeight`; then
  `∫ κ dρ = ρ(U)` with `0 < ρ(U) < ∞` from the disintegration, and `C' = C ρ(U)`.
- `dual_inner_integral`: when `lastWeight 1 = 1`, the inner integral at `[A]` is
  `χ(det w) χ(det A)⁻¹ |det A|^(s-1/2) W(M(diag(A,1))) ∫ S2(rev x) f̃([[A,0],[x,1]]) dx`.

This is the source's reduction (5)–(9) in the Library's lower-block coordinates. The
normalizations (6)–(7) of the weights become the hypothesis that `lastWeight` is the
indicator of integral units. The `t`-integral of the source becomes the constant `ρ(U)`.
