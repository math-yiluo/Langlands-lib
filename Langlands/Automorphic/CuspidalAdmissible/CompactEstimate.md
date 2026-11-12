# The compact estimate

Module: `Langlands.Automorphic.CuspidalAdmissible.CompactEstimate` (namespace
`Langlands.Global`). Provenance: internal; this is the classical argument that on a compact set
a smooth function is controlled by finitely many local averages up to a small multiple of the
square integrals of its derivatives (smoothing plus equicontinuity of the smoothed function).

Notation: `ν` is a left- and right-invariant measure on `GL_n(𝔸)`, finite on compact sets and
positive on open sets, `L'` a compact open subgroup of the finite adelic group, `Kc` compact,
`U = expBox δ L'` and `W₁ = expBox 1 L'` (module `ExpNeighbourhood`), `A_U φ(g)` the average
of `φ(g u)` over `u ∈ U` (module `CompactGeneric`). The functions `φ` are continuous,
right `L'`-invariant, with continuous derivatives `dφ_k` as in `exists_exp_pointwise`.

- `exists_conj_norm_bound`: a constant `CU` with `‖c⁻¹ Y c‖ ≤ CU ‖Y‖` for the coordinate matrix
  `c` of `exp Z`, `‖Z‖ ≤ 1` (continuity on the closed unit ball).
- `expBox_mono`, `ofInfinite_expInf_mem_expBox`, `one_mem_expBox`: elementary facts on boxes.
- `smoothing_bound` (one translate): for `u ∈ expBox δ L'`, `δ ≤ 1`,
  `∫_Kc |φ - φ(· u)|² dν ≤ (Cb δ)² ∑_k ∫_{Kc W₁} |dφ_k|² dν`. Write `u = exp(Z) l`; right
  `L'`-invariance removes `l`; the pointwise estimate along `t ↦ g exp(tZ)` and
  `setLIntegral_right_translates_le` (right invariance) conclude.
- `equicontinuity_bound`: for `p ∈ Kc`, `w ∈ expBox η L'` with `η ≤ 1`,
  `|A_U φ(p w) - A_U φ(p)|² ≤ (Cb CU η)² ν(U)⁻¹ ∑_k ∫_{Kc W₁ W₁} |dφ_k|² dν`. Jensen
  (`enorm_average_sub_sq_le`) reduces to `|φ(p w u) - φ(p u)|²` for `u ∈ U`; writing
  `w = exp(Z_w) l_w`, conjugation by `u` turns `w u` into `u · exp(Z') · l'` with
  `‖Z'‖ ≤ CU η` and `l' ∈ L'` (`conj_ofInfinite`, `conj_ofFinite`, `conj_expInf`), so the
  pointwise estimate applies along the curve `t ↦ p exp(t Z_w) u`; left invariance
  (`setLIntegral_translates_le`) bounds the integral over `u ∈ U ⊆ W₁` by the integral over
  `p W₁ W₁ ⊆ Kc W₁ W₁`.
- `mul_sq_le_of_le_div`: an elementary real inequality used to choose `δ` and `η`.
- `exists_compact_estimate K n ν L' hL'o hL'c Kc hKc`: there is a compact `K₃` (namely
  `Kc W₁ W₁`) such that for every `ε > 0` there are a compact `U` with `ν U ≠ 0`, a finite set
  `P ⊆ Kc` and a finite `C` with

  `∫_Kc |φ|² dν ≤ ε ∑_k ∫_{K₃} |dφ_k|² dν + C ∑_{p ∈ P} |A_U φ(p)|²`

  for every such `φ`. Proof: `δ = min(1, ε/(4(Cb²+1)))`, `U = expBox δ L'` (a neighbourhood of
  `1`, so `ν U > 0`), `η = min(1, ε/(2(c₀(Cb CU)²+1)))` with `c₀ = 4 ν(Kc) ν(U)⁻¹`, and `P` a
  finite net of `Kc` for `expBox η L'` (`exists_finite_net`). Then
  `|φ|² ≤ 2|A_U φ|² + 2|φ - A_U φ|²`, `|A_U φ(p w)|² ≤ 2|A_U φ(p)|² + 2|A_U φ(p w) - A_U φ(p)|²`,
  the smoothing bound with `lintegral_sub_average_le`, and the equicontinuity bound give the
  estimate with `C = 4 ν(Kc)`.
