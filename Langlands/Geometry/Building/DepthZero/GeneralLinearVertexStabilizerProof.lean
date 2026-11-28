import Langlands.Geometry.Building.DepthZero.GeneralLinearStatement
import Langlands.Geometry.Building.DepthZero.GeneralLinear.Central

/-!
# Vertex parahorics of `GL_N` are compact stabilizers but not full stabilizers

This module proves `GeneralLinearVertexStabilizerStatement`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

open GeneralLinearParahoric

/-- A power `ϖ^N` of the uniformizer with `N ≥ 1` does not have valuation one. -/
theorem valuation_uniformizer_pow_ne_one {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] {N : ℕ} (hN : 1 ≤ N) :
    ValuativeRel.valuation F
      ((SplitTorusValuation.uniformizerUnit F ^ N : Fˣ) : F) ≠ 1 := by
  intro h
  have hmem : SplitTorusValuation.uniformizerUnit F ^ N ∈ FML.unitGroup F :=
    (Valuation.mem_unitGroup_iff _ _ _).2 h
  rw [← Plancherel.fieldOrderUnits_ker, MonoidHom.mem_ker, map_pow] at hmem
  have h1 := congrArg Multiplicative.toAdd hmem
  rw [toAdd_pow, SplitTorusValuation.fieldOrderUnits_uniformizerUnit, toAdd_one] at h1
  have h2 : (N : ℤ) = 0 := by simpa using h1
  omega

/-- **Vertex parahorics of `GL_N` are compact stabilizers but not full stabilizers.** -/
theorem generalLinearVertexStabilizer : GeneralLinearVertexStabilizerStatement.{u} := by
  intro F _ _ _ _ N D hD y hy x hx
  have hG1 : D.base.zeroSubgroup = Plancherel.rationalCommonNormKernel
      (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)) :=
    le_antisymm D.base.zeroDatum.zeroSubgroup_le_rationalCommonNormKernel
      (rationalCommonNormKernel_le_zeroSubgroup D hD)
  have hpar : D.parahoric x = D.base.fixer y ⊓ Plancherel.rationalCommonNormKernel
      (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)) := by
    rw [D.parahoric_eq_pointwiseFixer_inf hD x, D.val_eq_singleton_of_isVertex hD hy x hx, hG1]
    congr 1
    exact KPApartmentData.pointwiseFixer_singleton _ y
  refine ⟨?_, fun hN => ?_⟩
  · rw [hpar]
    ext g
    rw [Subgroup.mem_inf, ValuationBuildingData.mem_compactStabilizer,
      ValuationBuildingData.mem_fixer]
    exact and_comm
  · refine lt_of_le_of_ne (hpar ▸ inf_le_left) fun heq => ?_
    have hz := scalarPoint_mem_fixer D.base.toValuationBuildingData
      (SplitTorusValuation.uniformizerUnit F) y
    rw [← heq, hpar] at hz
    have hv := valuation_det_eq_one hz.2
    rw [scalarPoint, MulEquiv.apply_symm_apply, det_diagGL, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, ← Units.val_pow_eq_pow_val] at hv
    exact valuation_uniformizer_pow_ne_one hN hv

end Langlands.Geometry.Building
