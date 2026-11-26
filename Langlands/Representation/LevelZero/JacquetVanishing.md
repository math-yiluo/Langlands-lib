# Vanishing of Jacquet coinvariants for level-zero induction

Lean module: `Langlands.Representation.LevelZero.JacquetVanishing`, namespace
`Langlands.LevelZero`.

## Block shapes

- `BlockShape.parabolic_ne_top_of_ne_top`: if the standard block parabolic of `B` is proper
  over a commutative ring `R`, it is proper over every field `S`. An element outside it has a
  nonzero entry in a block below the diagonal; the transvection with entry `1` at that position
  lies outside the parabolic over `S`.
- `BlockShape.conj_mem_unipotentSubgroup`: an element of the parabolic normalises its unipotent
  radical (`BlockShape.unipotentRadicalNormal`).

## Cuspidal sums

- `cuspidal_sum_eq_zero`: for a cuspidal representation `σ` of `GL_n(k)`
  (`FiniteGeneralLinear.IsCuspidal`) and a proper block shape `B`, the sum
  `∑ γ ∈ U_B(k), σ γ w` vanishes for every `w`, since it is fixed by `U_B(k)`.

## The level-zero indicator and the key vanishing

Fix a nonarchimedean local field `F`, a uniformizer `ϖ`, a complex representation `σ` of
`GL_{m+1}(k)`, and an open subgroup `L ≤ GL_{m+1}(𝒪_F)` on which reduction is trivial.

- `openSubgroup_le_inducingSubgroup` and `inducingRep_openSubgroup`: `L ≤ J` and `Λ` is trivial
  on `L`, where `J = inducingSubgroup m ϖ` and `Λ = inducingRep m hϖ σ`.
- `levelZeroIndicator hϖ σ L hLK hLred` is the linear map sending `v` to the smooth induced
  function `f_v` supported on `J` with `f_v(1) = v` (`indicatorLinear`).
- `exists_sum_translate_eq_zero`: if `σ` is cuspidal and the residue field is finite, then for
  every block shape `B` with `B.parabolic F ≠ ⊤`, every `g`, `y` and `v`, there are a nonempty
  finite type `ι` and `c : ι → B.conjugateUnipotent g` with
  `∑ i, π(c i) (π(y) f_v) = 0`, where `π` is `smoothInduced J Λ`.

**Proof of the key vanishing.** By the Iwasawa decomposition
(`Iwasawa.exists_iwasawa`), `g⁻¹ y = b κ` with `b = u · diag(ϖ^λ)` upper triangular and
`κ ∈ GL_{m+1}(𝒪_F)`; `b` lies in the standard parabolic of `B`
(`BlockShape.upperTriangularSubgroup_le_parabolic`). The index type is `U_B(k)`. For
`γ ∈ U_B(k)` let `γ̂` be its integral lift (`IntegralReduction.lift`), which lies in `U_B(F)`, and
put `c γ = g (b γ̂ b⁻¹) g⁻¹ ∈ g U_B g⁻¹`. Then `c γ · y = y · (κ⁻¹ γ̂ κ)` with
`κ⁻¹ γ̂ κ ∈ GL_{m+1}(𝒪_F)`, so `π(c γ) π(y) f_v = π(y) f_{w_γ}` with
`w_γ = σ(r κ)⁻¹ σ(γ) σ(r κ) v` by `smoothInduced_indicator`, where `r` is reduction. Summing,
`∑ γ w_γ = σ(r κ)⁻¹ (∑ γ σ(γ) σ(r κ) v) = 0` by `cuspidal_sum_eq_zero`, and linearity of
`v ↦ f_v` and of `π(y)` gives the claim.

Provenance: the vanishing of Jacquet modules of representations compactly induced from a
cuspidal type of level zero (Bushnell–Kutzko 1993, `bushnell-kutzko-1993-admissible-dual`,
SHA256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`, Theorem (6.2.2),
printed p. 203). The argument here is a direct computation with finite sums and does not follow
the source's proof.
