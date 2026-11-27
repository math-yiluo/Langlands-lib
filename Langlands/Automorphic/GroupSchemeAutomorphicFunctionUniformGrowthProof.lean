import Langlands.Automorphic.GroupSchemeAutomorphicFunctionUniformGrowthStatement
import Langlands.Automorphic.GroupSchemeInvariantFunctionGrowth

/-! # Uniformly moderate growth of automorphic functions on `Γ \ G(𝔸)`

A proof of `AutomorphicFunctionUniformGrowthStatement`. The Library's
`exists_uniformGrowth_functionInfiniteSlices` bounds all enveloping derivatives of all infinite
slices of a smooth, `Kinf`-finite, centre-finite function of moderate growth by one power of the
adelic height. Left invariance plays no role there, so the bound holds for every left subgroup
`Γ`. For a representation of positive size the adelic height is a fixed positive multiple of the
adelic source norm, and the constant absorbs that factor. -/

noncomputable section

universe u

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.InfiniteAdelicGroupPoints

/-- **Mœglin–Waldspurger 1995, I.2.17, for plain functions on `Γ \ G(𝔸)`.** For a connected
reductive group `G` over a number field, a maximal compact subgroup `Kinf` of the infinite adelic
points, a closed matrix representation `rho` with `0 < N` and an arbitrary subgroup `Γ` of
`G(𝔸)`, every function automorphic on `Γ \ G(𝔸)` has uniformly moderate growth. -/
theorem automorphicFunctionUniformGrowth : AutomorphicFunctionUniformGrowthStatement.{u} := by
  intro F _ _ G _ Γ Kinf N d rho hsmooth hcalc hG _hrho hK hN φ hφ
  obtain ⟨_, hsm, hKfin, hZfin, hgrowth⟩ := hφ
  obtain ⟨e, he, hbound⟩ := exists_uniformGrowth_functionInfiniteSlices F G hsmooth hcalc rho hN
    hG Kinf hK φ hsm.2.1 hKfin hZfin hgrowth
  let scale : ℝ := (N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult)
  have hscale : 0 < scale := pow_pos (Nat.cast_pos.mpr hN) _
  refine ⟨e, fun a => ?_⟩
  obtain ⟨C, hC, hCb⟩ := hbound a
  refine ⟨(C + 1) * scale ^ e, by positivity, fun b h x => ?_⟩
  let g := AdelicGroupPoints.pair F G x b
  have hsn : 0 ≤ RepresentationGrowth.adelicSourceNorm F G rho g ^ e :=
    Real.rpow_nonneg (RepresentationGrowth.adelicSourceNorm_pos F G rho hN g).le e
  have hheight : RepresentationGrowth.adelicHeight F G rho g ^ e =
      scale ^ e * RepresentationGrowth.adelicSourceNorm F G rho g ^ e := by
    rw [RepresentationGrowth.adelicHeight_eq_scalar_mul_sourceNorm,
      Real.mul_rpow hscale.le (RepresentationGrowth.adelicSourceNorm_pos F G rho hN g).le]
  have hle := hCb b x
  rw [hheight] at hle
  calc ‖(plotSmoothEnvelopingAction F G hsmooth hcalc a ⟨functionInfiniteSlice F G φ b, h⟩ :
          InfiniteAdelicGroupPoints F G → ℂ) x‖
      ≤ C * (scale ^ e * RepresentationGrowth.adelicSourceNorm F G rho g ^ e) := hle
    _ ≤ (C + 1) * (scale ^ e * RepresentationGrowth.adelicSourceNorm F G rho g ^ e) :=
        mul_le_mul_of_nonneg_right (by linarith)
          (mul_nonneg (Real.rpow_nonneg hscale.le e) hsn)
    _ = (C + 1) * scale ^ e * RepresentationGrowth.adelicSourceNorm F G rho g ^ e := by ring

end Langlands.Automorphic.GroupSchemeFunctions
