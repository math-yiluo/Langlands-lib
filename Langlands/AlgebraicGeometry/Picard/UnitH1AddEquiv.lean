import Langlands.AlgebraicGeometry.Picard.UnitH1LineBundleClassification
import Langlands.AlgebraicGeometry.Picard.CocycleLineBundleTensor

/-! # Additivity of the actual unit H¹ classification -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard

namespace UnitCechLineBundle

open Langlands.Cohomology Cech AbelianSheafCechH1

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)

/-- Adding ordered unit cochains multiplies their actual transition units. -/
lemma pairUnits_add (z w : C (unitP (X := X)) U 1) :
    pairUnits U (z + w) = pairUnits U z * pairUnits U w := by
  funext i j
  change (res (Cech.inter_two (U := U) i j).ge (z ![i, j] + w ![i, j])).toMul = _
  rw [map_add]
  rfl

/-- Tensoring glued closed unit cochains glues their sum on a full cover. -/
def tensorIso (hU : (⨆ i, U i) = ⊤) (z w : cocycles (unitP (X := X)) U) :
    Langlands.Scheme.Modules.tensorObj
      (CocycleGluing.glued (pairUnits U z.1))
      (CocycleGluing.glued (pairUnits U w.1)) ≅
      CocycleGluing.glued (pairUnits U (z + w).1) := by
  change _ ≅ CocycleGluing.glued (pairUnits U (z.1 + w.1))
  rw [pairUnits_add]
  exact CocycleGluing.tensorIso (isCocycle_pairUnits U z.2)
    (isCocycle_pairUnits U w.2) hU

/-- Gluing a sum represents the sum in the existing scheme Picard group. -/
lemma lineBundle_classOf_add (hU : (⨆ i, U i) = ⊤)
    (z w : cocycles (unitP (X := X)) U) :
    (lineBundle U hU (z + w).1 (z + w).2).classOf =
      (lineBundle U hU z.1 z.2).classOf + (lineBundle U hU w.1 w.2).classOf := by
  let L := lineBundle U hU z.1 z.2
  let M := lineBundle U hU w.1 w.2
  calc
    _ = Picard.classOf X (L.toInvertibleSheaf.tensor M.toInvertibleSheaf) :=
      (Picard.classOf_eq_iff X _ _).mpr
        ⟨(tensorIso U hU z w).symm ≪≫
          (Langlands.Scheme.Modules.localizedTensorIso X L.obj M.obj).symm⟩
    _ = _ := Picard.classOf_tensor X L.toInvertibleSheaf M.toInvertibleSheaf

end UnitCechLineBundle

namespace UnitCechH1Comparison

open Langlands.Cohomology AbelianSheafCechH1

variable {X : Scheme.{u}} {ι : Type u} [Finite ι] (U : ι → X.Opens)

/-- The actual H¹ class of a sum of finite-cover cocycles is their class sum. -/
lemma classOfCocycle_add (hU : (⨆ i, U i) = ⊤)
    (z w : cocycles (unitSheaf X).1 U) :
    classOfCocycle U hU (z + w) =
      classOfCocycle U hU z + classOfCocycle U hU w := by
  exact (comparisonHom (unitSheaf X) U hU.ge).map_add
    (QuotientAddGroup.mk z) (QuotientAddGroup.mk w)

end UnitCechH1Comparison

namespace Group

open Langlands.Cohomology AbelianSheafCechH1 AbelianSheafH1Refinement
open UnitCechH1Comparison UnitCechRefinement

variable {X : Scheme.{u}} [CompactSpace X]

/-- The published actual H¹ classifier respects the existing Picard group addition. -/
lemma unitCohomologyClass_add (x y : Group X) :
    unitCohomologyClass (x + y) = unitCohomologyClass x + unitCohomologyClass y := by
  let L := lineBundleRepresentative X x
  let M := lineBundleRepresentative X y
  let D := L.finiteUnitPresentation
  let E := M.finiteUnitPresentation
  let W := commonCover D.cover.U E.cover.U
  have hW : (⨆ p, W p) = ⊤ :=
    commonCover_eq_top D.cover.U E.cover.U D.cover.iSup_eq_top E.cover.iSup_eq_top
  let z := refineCocycles (unitSheaf X).1 D.cover.U W Prod.fst
    (fun _ => inf_le_left) ⟨D.cochain, D.closed⟩
  let w := refineCocycles (unitSheaf X).1 E.cover.U W Prod.snd
    (fun _ => inf_le_right) ⟨E.cochain, E.closed⟩
  have hx : (UnitCechLineBundle.lineBundle W hW z.1 z.2).classOf = x := by
    calc
      _ = L.classOf := (LineBundle.classOf_eq_iff _ _).mpr
        ⟨(refinementIso D.cover.U W Prod.fst (fun _ => inf_le_left)
          hW D.cochain D.closed).symm ≪≫ D.cochainIso.symm⟩
      _ = x := classOf_lineBundleRepresentative X x
  have hy : (UnitCechLineBundle.lineBundle W hW w.1 w.2).classOf = y := by
    calc
      _ = M.classOf := (LineBundle.classOf_eq_iff _ _).mpr
        ⟨(refinementIso E.cover.U W Prod.snd (fun _ => inf_le_right)
          hW E.cochain E.closed).symm ≪≫ E.cochainIso.symm⟩
      _ = y := classOf_lineBundleRepresentative X y
  have hz : unitCohomologyClass x = classOfCocycle W hW z := by
    rw [← hx, unitCohomologyClass_classOf, LineBundle.unitCohomologyClass_glued]
  have hw : unitCohomologyClass y = classOfCocycle W hW w := by
    rw [← hy, unitCohomologyClass_classOf, LineBundle.unitCohomologyClass_glued]
  calc
    _ = unitCohomologyClass
        (UnitCechLineBundle.lineBundle W hW (z + w).1 (z + w).2).classOf := by
      rw [UnitCechLineBundle.lineBundle_classOf_add, hx, hy]
    _ = classOfCocycle W hW (z + w) := by
      rw [unitCohomologyClass_classOf, LineBundle.unitCohomologyClass_glued]
    _ = classOfCocycle W hW z + classOfCocycle W hW w := classOfCocycle_add W hW z w
    _ = _ := by rw [hz, hw]

/-- The existing scheme Picard group is additively equivalent to actual unit H¹. -/
def unitCohomologyAddEquiv (X : Scheme.{u}) [CompactSpace X] :
    Group X ≃+ Sheaf.H.{u} (unitSheaf X) 1 where
  __ := unitCohomologyEquiv X
  map_add' := unitCohomologyClass_add

@[simp] lemma unitCohomologyAddEquiv_apply (x : Group X) :
    unitCohomologyAddEquiv X x = unitCohomologyClass x := rfl

@[simp] lemma unitCohomologyAddEquiv_classOf (L : LineBundle X) :
    unitCohomologyAddEquiv X L.classOf = L.unitCohomologyClass :=
  unitCohomologyClass_classOf L

@[simp] lemma unitCohomologyClass_zero :
    unitCohomologyClass (0 : Group X) = 0 :=
  (unitCohomologyAddEquiv X).map_zero

@[simp] lemma unitCohomologyClass_neg (x : Group X) :
    unitCohomologyClass (-x) = -unitCohomologyClass x :=
  (unitCohomologyAddEquiv X).map_neg x

end Group

end Langlands.AlgebraicGeometry.Picard
