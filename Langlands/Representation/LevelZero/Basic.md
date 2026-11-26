# The inducing datum of a level-zero representation of `GL_{m+1}(F)`

Lean module: `Langlands.Representation.LevelZero.Basic`, namespace `Langlands.LevelZero`.

Let `F` be a nonarchimedean local field (Mathlib's `IsNonarchimedeanLocalField`).

## Integers and reduction

- `integers F` is the valuation ring `(ValuativeRel.valuation F).integer`.
  `mem_maximalIdeal_iff`: an integer lies in the maximal ideal exactly when its valuation is
  less than `1`. `residue_eq_residue_iff`: two integers have the same residue exactly when
  their difference has valuation less than `1`.
- `maximalCompact m` is `GL_{m+1}(𝒪_F)`, the Library's `Conductor.integralSubgroup`, and
  `residueReduction m` its reduction to `GL_{m+1}` of the residue field
  (`IntegralReduction.reduction`).

## The inducing subgroup and representation

- `uniformizerScalar m ϖ` is the scalar matrix `ϖ · 1`; it is central
  (`uniformizerScalar_mem_center`) and `uniformizerScalar_zpow` computes its powers.
- `zpow_mem_maximalCompact`: for a uniformizer `ϖ`
  (`Iwasawa.IsUniformizingElement (valuation F) ϖ`), `(ϖ · 1) ^ a` is integral only for
  `a = 0`, because both `v(ϖ)^a` and `v(ϖ)^(-a)` would be at most `1`.
- `inducingSubgroup m ϖ` is `J = ϖ^ℤ GL_{m+1}(𝒪_F)` (`LevelZero.powerProduct`), and
  `inducingRep m hϖ σ` is the representation of `J` obtained from a complex representation `σ`
  of `GL_{m+1}(k)` by inflation along `residueReduction m` and extension with `ϖ · 1` acting
  trivially. `inducingRep_of_mem` and `inducingRep_zpow_mul` compute it.

## An open subgroup in the kernel of reduction

- `nearIdentity m` is the set of `g` such that every entry of `g - 1` and of `g⁻¹ - 1` has
  valuation less than `1`. It is a neighbourhood of `1` (`nearIdentity_mem_nhds`): each condition
  is the preimage, under a continuous entry map sending `1` to `0`, of the neighbourhood
  `{x | v x < 1}` of `0` given by `IsValuativeTopology.mem_nhds_zero_iff`.
- `nearIdentity_subset_maximalCompact`: such `g` and `g⁻¹` have integral entries, by the
  ultrametric inequality; `residueReduction_eq_one_of_near`: their reduction is `1`.
- `exists_openSubgroup_reduction_trivial`: there is an open subgroup `L ≤ GL_{m+1}(𝒪_F)` on which
  reduction is trivial; it is a compact open subgroup inside `nearIdentity m`
  (`LocalFieldTopology.generalLinear_compactOpen`).

Provenance: the inflation of a representation of `GL_N(k)` to `GL_N(𝔬_F)` and its extension to
`F^× GL_N(𝔬_F)` are the level-zero types of Bushnell–Kutzko 1993
(`bushnell-kutzko-1993-admissible-dual`, SHA256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`, Chapter 5; Theorem (6.2.2),
printed p. 203, PDF p. 215). Here only the central element `ϖ · 1` is adjoined, rather than the
whole centre `F^×`; the remaining central elements `u · 1`, `u ∈ 𝒪_F^×`, already lie in
`GL_{m+1}(𝒪_F)`.
