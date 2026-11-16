# Regularity and invariance of the rectangle periods

Module `Langlands.Global.RankinSelberg.DualExpansionInduction`, namespace
`Langlands.Global.RankinSelbergGlobal.Unfolding`.

Provenance: internal.

- `lastEntry`: continuity, additivity, periodicity of `ψ ∘ lastEntry` for `ψ` trivial on `F`
  (`isPeriodic_lastEntry`), and invariance under unitriangular matrices
  (`lastEntry_mulVec_unitriangular`).
- `ratMulVec_kron` and `surjective_ratMulVec_kron`: the action of `M ∈ GL_K(F)` on rectangles by
  left multiplication is the Kronecker product `M ⊗ I_m` acting on vectors.
- `rectInner ψ G g x = T_c ψ(lastEntry c) G(x̂ ĉ g)` (`rectPeriod_eq_rectInner`), its
  periodicity and joint continuity in a parameter (`DualData.isPeriodic_rectInner`,
  `DualData.continuous_rectInner_param`, `DualData.continuous_rectPeriod_param`,
  `DualData.continuous_rectInner`).
- `DualData.rectPeriod_midPoint_rat_mul`: the rectangle period of the corner sum at
  `diag(I, g u, 1) y` does not depend on `g ∈ N_K(F)`. The proof conjugates `x̂ĉ` by the middle
  block and changes variables in both torus integrals by the rational linear maps
  `c ↦ g⁻¹ c` and `x ↦ g⁻¹ x`.
