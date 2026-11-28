# Proof: vertex parahorics of `GL_N` are compact stabilizers but not full stabilizers

Module `Langlands.Geometry.Building.DepthZero.GeneralLinearVertexStabilizerProof`.

The theorem `Langlands.Geometry.Building.generalLinearVertexStabilizer` proves
`Langlands.Geometry.Building.GeneralLinearVertexStabilizerStatement` at every universe `u`: for
a nonarchimedean local field `F`, every `N`, every `D : KPBuildingDatum` of `GL_N` over `F` with
`D.SatisfiesGroupAxioms`, every vertex `y` of the reduced building and the facet `x` containing
`y`, the parahoric `D.parahoric x` is the compact stabilizer `D.base.compactStabilizer y`
(`G(F)^1 ∩ G(F)_y`), and if `N ≥ 1` it is a proper subgroup of the full stabilizer
`D.base.fixer y`. It adds no premise.

The auxiliary theorem `valuation_uniformizer_pow_ne_one` states that `ϖ^N` does not have
valuation one when `N ≥ 1`, for the uniformizer `SplitTorusValuation.uniformizerUnit F`: its
order is `N` (`SplitTorusValuation.fieldOrderUnits_uniformizerUnit`), while the units of
valuation one are the kernel of the order (`Plancherel.fieldOrderUnits_ker`).

## Proof

1. `G(F)^0 = G(F)^1`: `ZeroSubgroupDatum.zeroSubgroup_le_rationalCommonNormKernel` gives `≤`,
   and `GeneralLinearParahoric.rationalCommonNormKernel_le_zeroSubgroup` gives `≥`.
2. `D.parahoric x = G(F)_y ∩ G(F)^1`: the parahoric is the pointwise fixer of the facet
   intersected with `G(F)^0` (`KPBuildingDatum.parahoric_eq_pointwiseFixer_inf`, Axiom 4.1.20),
   the facet is `{y}` (`KPBuildingDatum.val_eq_singleton_of_isVertex`), and the pointwise fixer
   of `{y}` is the fixer of `y` (`KPApartmentData.pointwiseFixer_singleton`).
3. The first conjunct follows from `ValuationBuildingData.mem_compactStabilizer`.
4. For `N ≥ 1`, `D.parahoric x ≤ G(F)_y` by step 2. The scalar matrix `ϖ · 1` fixes `y`
   (`GeneralLinearParahoric.scalarPoint_mem_fixer`); if the two subgroups were equal it would
   lie in `G(F)^1`, so its determinant `ϖ^N` would have valuation one
   (`GeneralLinearParahoric.valuation_det_eq_one`, `GeneralLinearParahoric.det_diagGL`),
   contradicting `valuation_uniformizer_pow_ne_one`.

## Sources

Tasho Kaletha and Gopal Prasad, *Bruhat–Tits Theory: A New Approach*, Cambridge University
Press, 2023 (PDF page = printed page + 31): 15.1.33 (printed p. 524, PDF p. 555) for
`G(k)^0 = G(k)^1` for `GL(X)` and the trivial action of the scalars; Theorem 4.2.15 (printed
p. 173, PDF p. 204) for the compact stabilizers. Literature ID
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`. The Lean proof does not
follow the source's route through lattices: it compares `G(F)^0` with `G(F)^1` through the zero
datum and the root groups of the datum, as described in the modules it imports.
