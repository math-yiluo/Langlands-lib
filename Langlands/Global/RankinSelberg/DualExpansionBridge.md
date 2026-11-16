# The coefficient along `Y_(n,m)` of a dual function is a dual period

Module `Langlands.Global.RankinSelberg.DualExpansionBridge`, namespace
`Langlands.Global.RankinSelbergGlobal.Unfolding`.

Provenance: internal.

- `rectCoordHom`, `torusIntegral_rectCoords`: the linear change of variables
  `A ↦ (rectX A, rectC A)` preserves torus integrals: `T_A h(rectX A, rectC A) = T_X T_c h(X, c)`
  for continuous periodic `h`.
- `iota_mem_rationalSubgroup_of_mem`; continuity and periodicity of the rectangle integrand
  (`DualData.continuous_rectIntegrand`, `DualData.periodic_rectIntegrand`).
- **`DualData.coefficient_eq_dualPeriod`**: let `W` be a `DualData` function at rank
  `n = m + K + 1` whose corner sum `S` is left invariant under `GL_n(F)`. Then the Library's
  coefficient `subgroupCharacterCoefficient` along `Y_(n,m)` with `projectionCharacter`, of
  `g ↦ S(ᵗg⁻¹)`, at `x`, equals `dualPeriod F m K ψ W (w · ᵗx⁻¹)`, `w = wPoint`.

Proof: `coefficient_eq_iterated` writes the coefficient as an iterated period over `N_K` and the
rectangle coordinates. `wPoint_iota_conj` and the `GL_n(F)`-invariance of `S` (for `w`) turn the
integrand into `ψ(superSum (dualConj u)) ψ(lastEntry c) S(x̂ ĉ · diag(I, dualConj u, 1) · w ᵗx⁻¹)`;
`torusIntegral_rectCoords` gives the rectangle period, and the Library's
`setIntegral_comp_dualConjUnipotent` removes `dualConj` from the period over `N_K`.
