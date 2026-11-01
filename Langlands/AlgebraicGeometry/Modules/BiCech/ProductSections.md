# Cup maps on Čech cochains of the factors

Author: Worker 1147.

Lean module: `Langlands.AlgebraicGeometry.Modules.BiCech.ProductSections`.
It is a helper for the proof of
`Langlands.AlgebraicGeometry.Modules.CoherentFieldExternalTensorKunnethStatement`.

The setting is that of `BiCech.CupBijective`, with ordered affine covers `𝒰` of `X` and
`𝒱` of `Y`.

## Definitions

- `prodBiCover p₁ p₂ 𝒰 𝒱 : BiCover P`. Its opens `biOpen s t` are
  `p₁⁻¹(𝒰.inter s) ⊓ p₂⁻¹(𝒱.inter t)`.
- `cup_zsmul_left`, `cup_zsmul_right`, `cup_sum_left` and `cup_sum_right` give additivity
  of the cup map.
- `cupFam hπ hP 𝒰 𝒱 L M p q` is the `R`-linear map
  `C^p(𝒰, L) ⊗[R] C^q(𝒱, M) → ∏_{s, t} (p₁^* L ⊗ p₂^* M)(biOpen s t)`. Here `C^p(𝒰, L)` is
  the Library's cochain module `(OModulePresheaf.ofModules πX L).cochain 𝒰 p`. The `(s, t)`
  component of `cupFam` is `cupLin` after projecting both factors (`cupFam_tmul`).

## Bijectivity

`cupFam_bijective`: assume every `𝒰.inter s` (`s : 𝒰.Idx p`) and every `𝒱.inter t`
(`t : 𝒱.Idx q`) is affine and carries a frame. Then `cupFam p q` is bijective. The proof
follows the Library's `FieldTwoAxisH1Injectivity.tensorFam_bijective`:
`TensorProduct.piLeft` and `TensorProduct.piRight` identify the source with
`∏_{s, t} L(𝒰.inter s) ⊗ M(𝒱.inter t)`, and `cupLin_bijective` applies componentwise.

## Differentials

- `dΓ` and `dΓ'` are the Čech differentials of families of sections of `L` and `M`.
  `d_eq_dΓ` and `d_eq_dΓ'` identify them with the cochain differentials
  `OModulePresheaf.d` of the Library.
- `cupFamFun a b s t = cup (a s) (b t)` is the same map, stated at the level of sections.
  `cupFam_tmul'` states `cupFam (a ⊗ₜ b) = cupFamFun a b`.
- `horF_cupFamFun : horF (cupFamFun a b) = cupFamFun (dΓ a) b` and `verF_cupFamFun`
  (`verF (cupFamFun a b) = cupFamFun a (dΓ' b)`) state that the cup map turns the factor
  differentials into the bi-Čech differentials. They follow from the additivity and
  restriction compatibility of the cup map.

Provenance: internal.
