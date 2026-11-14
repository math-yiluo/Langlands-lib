import Langlands.Geometry.Building.Kottwitz.TorusMap
import Langlands.Geometry.Building.KPZeroDatumConstruction
import Mathlib.FieldTheory.PrimitiveElement

/-! # A splitting extension normal over the local ground field -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building.Kottwitz

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (T : CommGroupScheme (Spec (CommRingCat.of F)))

/-- A finite Galois splitting field over `K` can also be chosen normal over `F`. -/
theorem exists_normal_splitting (hT : IsTorus T.toGrp) :
    ∃ L : IntermediateField (UnramifiedClosure F) (SeparableClosure F),
      FiniteDimensional (UnramifiedClosure F) L ∧ IsGalois (UnramifiedClosure F) L ∧
      Normal F L ∧ IsSplitTorus (baseChanged F L T.toGrp) := by
  obtain ⟨M, hfin, hgal, hM⟩ :=
    exists_finiteGaloisSplittingField_inside (SeparableClosure F) T.toGrp hT
  let : FiniteDimensional F M := hfin
  let : IsGalois F M := hgal
  obtain ⟨a, ha⟩ := Field.exists_primitive_element F M
  have ha' : IntermediateField.adjoin F {(a : SeparableClosure F)} = M := by
    have h := congrArg (fun N : IntermediateField F M => N.map M.val) ha
    change IntermediateField.adjoin F {M.val a} = M
    simpa only [IntermediateField.adjoin_map, Set.image_singleton,
      ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val] using h
  let L := IntermediateField.adjoin (UnramifiedClosure F) {(a : SeparableClosure F)}
  have hL : L.restrictScalars F = Langlands.LocalGalois.Separable.inertiaFixedField F ⊔ M := by
    change (IntermediateField.adjoin (Langlands.LocalGalois.Separable.inertiaFixedField F)
      {(a : SeparableClosure F)}).restrictScalars F = _
    rw [IntermediateField.restrictScalars_adjoin_eq_sup, ha']
  let : FiniteDimensional (UnramifiedClosure F) L :=
    IntermediateField.adjoin.finiteDimensional
      (Algebra.IsIntegral.isIntegral (R := UnramifiedClosure F) (a : SeparableClosure F))
  let : Normal F L := by
    change Normal F (L.restrictScalars F)
    rw [hL]
    infer_instance
  let : Normal (UnramifiedClosure F) L :=
    Normal.tower_top_of_normal F (UnramifiedClosure F) L
  let : IsGalois (UnramifiedClosure F) L := ⟨⟩
  have hML : M ≤ L.restrictScalars F := hL ▸ le_sup_right
  let i : M →ₐ[F] L := IntermediateField.inclusion hML
  let alg : Algebra M L := i.toRingHom.toAlgebra
  let : SMul M L := alg.toSMul
  let : Algebra M L := alg
  let : IsScalarTower F M L := IsScalarTower.of_algebraMap_eq (R := F) (S := M) (A := L) fun _ => rfl
  exact ⟨L, inferInstance, inferInstance, inferInstance,
    IsSplitTorus.baseChange_fieldTower F M L T.toGrp hM⟩

end Langlands.Geometry.Building.Kottwitz
