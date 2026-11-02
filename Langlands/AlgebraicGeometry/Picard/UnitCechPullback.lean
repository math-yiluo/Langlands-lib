import Langlands.Cohomology.CechPullback
import Langlands.AlgebraicGeometry.Picard.UnitCechLineBundle
import Langlands.AlgebraicGeometry.Picard.CocycleLineBundlePullback
import Langlands.AlgebraicGeometry.Picard.LineBundleInverse

/-! # Pullback of ordered actual-unit cocycles -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard.UnitCechPullback

open Langlands.Cohomology Cech AbelianSheafCechH1 UnitCechLineBundle

variable {X Y : Scheme.{u}} (q : Y ⟶ X) {ι : Type u} (U : ι → X.Opens)

/-- The actual structure-sheaf unit map into the pushed-forward units. -/
def unitsMap :
    unitP (X := X) ⟶ (Opens.map q.base).op ⋙ unitP (X := Y) :=
  Functor.whiskerRight q.c NilpotentUnitReduction.ringUnitsFunctor

/-- Pullback of actual-unit cochains, including transport to the preimage intersections. -/
def cochains (p : ℕ) :
    C (unitP (X := X)) U p →+ C (unitP (X := Y)) (fun i => q ⁻¹ᵁ U i) p :=
  (CechPullback.cochains q.base (unitP (X := Y)) U p).toAddMonoidHom.comp
    (Cech.map U (unitsMap q) p)

lemma cochains_apply (p : ℕ) (z : C (unitP (X := X)) U p)
    (σ : Fin (p + 1) → ι) :
    cochains q U p z σ =
      res (P := unitP (X := Y)) (CechPullback.inter_preimage q.base U σ).le
        ((unitsMap q).app (op (inter U σ)) (z σ)) := rfl

/-- Actual-unit cochain pullback commutes with the ordered differential. -/
lemma d_cochains (p : ℕ) (z : C (unitP (X := X)) U p) :
    d (unitP (X := Y)) (fun i => q ⁻¹ᵁ U i) p (cochains q U p z) =
      cochains q U (p + 1) (d (unitP (X := X)) U p z) := by
  change d _ _ p (CechPullback.cochains q.base _ U p (Cech.map U (unitsMap q) p z)) = _
  rw [CechPullback.d_cochains, Cech.d_map]
  rfl

lemma closed_cochains {z : C (unitP (X := X)) U 1}
    (hz : d (unitP (X := X)) U 1 z = 0) :
    d (unitP (X := Y)) (fun i => q ⁻¹ᵁ U i) 1 (cochains q U 1 z) = 0 := by
  rw [d_cochains, hz, map_zero]

/-- The homomorphism on actual-unit one-cocycles. -/
def mapCocycles :
    cocycles (unitP (X := X)) U →+
      cocycles (unitP (X := Y)) (fun i => q ⁻¹ᵁ U i) :=
  (CechPullback.cocyclesEquiv q.base (unitP (X := Y)) U).toAddMonoidHom.comp
    (AbelianSheafH1Naturality.mapCocycles U (unitsMap q))

/-- The induced homomorphism on the existing fixed-cover Čech H¹ quotient. -/
def mapH1 :
    CechH1 (unitP (X := X)) U →+
      CechH1 (unitP (X := Y)) (fun i => q ⁻¹ᵁ U i) :=
  (CechPullback.h1Equiv q.base (unitP (X := Y)) U).toAddMonoidHom.comp
    (AbelianSheafH1Naturality.mapHom U (unitsMap q))

lemma mapH1_mk (z : cocycles (unitP (X := X)) U) :
    mapH1 q U (QuotientAddGroup.mk z) = QuotientAddGroup.mk (mapCocycles q U z) := rfl

/-- The ordered pullback gives precisely the published pulled transition units. -/
lemma pairUnits_cochains (z : C (unitP (X := X)) U 1) :
    pairUnits (fun i => q ⁻¹ᵁ U i) (cochains q U 1 z) =
      CocycleGluing.pullbackCocycle q (pairUnits U z) := by
  funext i j
  apply Units.ext
  change unitVal (res _ (cochains q U 1 z ![i, j])) = _
  rw [cochains_apply, res_res]
  change Y.presheaf.map (homOfLE _).op
      (q.app (inter U ![i, j]) (unitVal (z ![i, j]))) =
    q.appLE (U i ⊓ U j) _ le_rfl
      (X.presheaf.map (homOfLE (Cech.inter_two (U := U) i j).ge).op
        (unitVal (z ![i, j])))
  rw [CocycleGluing.res_app, CocycleGluing.appLE_res]

/-- Pullback commutes with gluing an ordered actual-unit cocycle on a full cover. -/
def pullbackIso (hU : (⨆ i, U i) = ⊤) (z : C (unitP (X := X)) U 1)
    (hz : d (unitP (X := X)) U 1 z = 0) :
    (Scheme.Modules.pullback q).obj (lineBundle U hU z hz).obj ≅
      (lineBundle (fun i => q ⁻¹ᵁ U i) (q.iSup_preimage_eq_top hU)
        (cochains q U 1 z) (closed_cochains q U hz)).obj := by
  change (Scheme.Modules.pullback q).obj (CocycleGluing.glued (pairUnits U z)) ≅
    CocycleGluing.glued (pairUnits (fun i => q ⁻¹ᵁ U i) (cochains q U 1 z))
  rw [pairUnits_cochains]
  exact CocycleGluing.pullbackIso q _ hU (isCocycle_pairUnits U hz)

/-- The actual Picard pullback of the glued bundle is the class of the pulled cocycle. -/
lemma pullback_classOf (hU : (⨆ i, U i) = ⊤) (z : C (unitP (X := X)) U 1)
    (hz : d (unitP (X := X)) U 1 z = 0) :
    Group.pullback q (lineBundle U hU z hz).classOf =
      (lineBundle (fun i => q ⁻¹ᵁ U i) (q.iSup_preimage_eq_top hU)
        (cochains q U 1 z) (closed_cochains q U hz)).classOf := by
  rw [Group.pullback_lineBundle_classOf]
  exact (LineBundle.classOf_eq_iff _ _).2 ⟨pullbackIso q U hU z hz⟩

end Langlands.AlgebraicGeometry.Picard.UnitCechPullback
