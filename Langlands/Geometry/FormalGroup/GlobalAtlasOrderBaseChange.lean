import Langlands.Geometry.FormalGroup.AtlasOrderBaseChangeAlong
import Langlands.Geometry.FormalGroup.GlobalAtlasOrderAction
import Langlands.Geometry.FormalGroup.OrderIso

/-! # Actual coefficient-extension comparisons for global order covers -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ : Type} [Finite σ] {M : ModuleLaw O R σ}

/-- The complete acting order is compatible with actual successive scalar extension. -/
def OrderAction.mapCompIso (E : OrderAction D M)
    {S T : Type v} [CommRing S] [CommRing T] [Algebra O S] [Algebra O T]
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) :
    OrderAction.Iso ((E.map f).map g) (E.map (g.comp f)) :=
  OrderAction.Iso.ofModuleIso (ModuleLaw.mapCompIso M f g) (by
    intro d
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change CoordinateMap.id.comp
      (((E.action d).toHom.toCoordinateMap.map f.toRingHom).map g.toRingHom) =
      ((E.action d).toHom.toCoordinateMap.map (g.comp f).toRingHom).comp CoordinateMap.id
    rw [CoordinateMap.id_comp, CoordinateMap.comp_id, CoordinateMap.map_ringHom_comp]
    rfl)

namespace BasicAtlas

variable (E : ModuleLaw.OrderAction D M) (s : Set R) (hs : Ideal.span s = ⊤)
variable (S : CommAlgCat.{v} R)

set_option backward.isDefEq.respectTransparency false in
/-- Extending a restricted global order chart compares to restricting the extended global action. -/
def globalCoverBaseChartIso (A : CommAlgCat.{v} S)
    (b : (ofGlobalCover M s hs).baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) :
    ModuleLaw.OrderAction.Iso
      ((((ofGlobalCoverOrderAction E s hs).baseChange S).chart b).map
        (coefficientLift (O := O) b.val A hb))
      (((ofGlobalCoverOrderAction (E.map (IsScalarTower.toAlgHom O R S))
        ((ofGlobalCover M s hs).baseOpens S) ((ofGlobalCover M s hs).baseOpens_covers S)).chart b).map
          (coefficientLift (O := O) b.val A hb)) :=
  ((ofGlobalCoverOrderAction E s hs).baseOrderChartIso S A b hb).trans
    ((globalOrderChartIso E ((ofGlobalCover M s hs).baseSource S b).val
      (restrictTest S A) ((ofGlobalCover M s hs).baseSource_unit S A b hb)).trans
        ((E.mapCompIso (IsScalarTower.toAlgHom O R S)
          (IsScalarTower.toAlgHom O S A)).symm.trans
            (globalOrderChartIso (E.map (IsScalarTower.toAlgHom O R S)) b.val A hb).symm))

/-- The forward map retains the actual identity coordinate series. -/
theorem globalCoverBaseChartIso_hom_coordinates (A : CommAlgCat.{v} S)
    (b : (ofGlobalCover M s hs).baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) :
    (globalCoverBaseChartIso E s hs S A b hb).hom.val.toHom.toCoordinateMap = CoordinateMap.id := by
  change ((CoordinateMap.id.comp CoordinateMap.id).comp CoordinateMap.id).comp CoordinateMap.id = _
  simp only [CoordinateMap.id_comp]

/-- The inverse retains the actual identity coordinate series as well. -/
theorem globalCoverBaseChartIso_inv_coordinates (A : CommAlgCat.{v} S)
    (b : (ofGlobalCover M s hs).baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) :
    (globalCoverBaseChartIso E s hs S A b hb).inv.val.toHom.toCoordinateMap = CoordinateMap.id := by
  change CoordinateMap.id.comp (CoordinateMap.id.comp (CoordinateMap.id.comp CoordinateMap.id)) = _
  simp only [CoordinateMap.id_comp]

/-- A global cover's actual transitions have identity series. -/
theorem globalTransition_hom_coordinates (N : ModuleLaw O R σ) (A : CommAlgCat.{v} R)
    (a b : R) (ha : IsUnit (algebraMap R A a)) (hb : IsUnit (algebraMap R A b)) :
    (globalTransition N A a b ha hb).hom.toHom.toCoordinateMap = CoordinateMap.id := by
  change CoordinateMap.id.comp CoordinateMap.id = _
  exact CoordinateMap.id_comp _

/-- The extended global cover's transitions still have identity series. -/
theorem globalCoverBaseTransition_coordinates (A : CommAlgCat.{v} S)
    (a b : (ofGlobalCover M s hs).baseOpens S)
    (ha : IsUnit (algebraMap S A a.val)) (hb : IsUnit (algebraMap S A b.val)) :
    ((ofGlobalCover M s hs).baseTransition S A a b ha hb).hom.toHom.toCoordinateMap = CoordinateMap.id := by
  rw [baseTransition_coordinates]
  exact globalTransition_hom_coordinates _ _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The actual coefficient-extended cover maps to the restricted extended global order action. -/
def globalCoverBaseHom :
    OrderAction.Hom ((ofGlobalCoverOrderAction E s hs).baseChange S)
      (ofGlobalCoverOrderAction (E.map (IsScalarTower.toAlgHom O R S))
        ((ofGlobalCover M s hs).baseOpens S) ((ofGlobalCover M s hs).baseOpens_covers S)) rfl :=
  ⟨{ hom A b hb := (globalCoverBaseChartIso E s hs S A b hb).hom.val
     natural φ b ha hb := by
       rw [globalCoverBaseChartIso_hom_coordinates E s hs S _ b ha,
         globalCoverBaseChartIso_hom_coordinates E s hs S _ b hb]
       exact CoordinateMap.map_id _
     transition A b c hb hc := by
       apply ModuleLaw.Hom.ext
       apply CommLaw.Hom.ext
       change (globalTransition _ A b.val c.val hb hc).hom.toHom.toCoordinateMap.comp
         (globalCoverBaseChartIso E s hs S A b hb).hom.val.toHom.toCoordinateMap =
         (globalCoverBaseChartIso E s hs S A c hc).hom.val.toHom.toCoordinateMap.comp
           ((ofGlobalCover M s hs).baseTransition S A b c hb hc).hom.toHom.toCoordinateMap
       rw [globalTransition_hom_coordinates,
         globalCoverBaseTransition_coordinates (M := M) s hs S A b c hb hc,
         globalCoverBaseChartIso_hom_coordinates, globalCoverBaseChartIso_hom_coordinates] },
   fun A b hb d => (globalCoverBaseChartIso E s hs S A b hb).hom.commutes d⟩

set_option backward.isDefEq.respectTransparency false in
/-- The same actual inverse chart maps give the reverse cover comparison. -/
def globalCoverBaseInv :
    OrderAction.Hom
      (ofGlobalCoverOrderAction (E.map (IsScalarTower.toAlgHom O R S))
        ((ofGlobalCover M s hs).baseOpens S) ((ofGlobalCover M s hs).baseOpens_covers S))
      ((ofGlobalCoverOrderAction E s hs).baseChange S) rfl :=
  ⟨{ hom A b hb := (globalCoverBaseChartIso E s hs S A b hb).inv.val
     natural φ b ha hb := by
       rw [globalCoverBaseChartIso_inv_coordinates E s hs S _ b ha,
         globalCoverBaseChartIso_inv_coordinates E s hs S _ b hb]
       exact CoordinateMap.map_id _
     transition A b c hb hc := by
       apply ModuleLaw.Hom.ext
       apply CommLaw.Hom.ext
       change ((ofGlobalCover M s hs).baseTransition S A b c hb hc).hom.toHom.toCoordinateMap.comp
         (globalCoverBaseChartIso E s hs S A b hb).inv.val.toHom.toCoordinateMap =
         (globalCoverBaseChartIso E s hs S A c hc).inv.val.toHom.toCoordinateMap.comp
           (globalTransition _ A b.val c.val hb hc).hom.toHom.toCoordinateMap
       rw [globalTransition_hom_coordinates,
         globalCoverBaseTransition_coordinates (M := M) s hs S A b c hb hc,
         globalCoverBaseChartIso_inv_coordinates, globalCoverBaseChartIso_inv_coordinates] },
   fun A b hb d => (globalCoverBaseChartIso E s hs S A b hb).inv.commutes d⟩

set_option backward.isDefEq.respectTransparency false in
/-- Global restriction and coefficient extension commute by actual full-order formal maps. -/
def globalCoverBaseIso :
    OrderAction.Iso ((ofGlobalCoverOrderAction E s hs).baseChange S)
      (ofGlobalCoverOrderAction (E.map (IsScalarTower.toAlgHom O R S))
        ((ofGlobalCover M s hs).baseOpens S) ((ofGlobalCover M s hs).baseOpens_covers S)) rfl where
  hom := globalCoverBaseHom E s hs S
  inv := globalCoverBaseInv E s hs S
  inv_hom := by
    apply Subtype.ext
    apply BasicAtlas.Hom.ext
    intro A b hb
    exact congrArg Subtype.val (globalCoverBaseChartIso E s hs S A b hb).inv_hom
  hom_inv := by
    apply Subtype.ext
    apply BasicAtlas.Hom.ext
    intro A b hb
    exact congrArg Subtype.val (globalCoverBaseChartIso E s hs S A b hb).hom_inv

end BasicAtlas

end Langlands.FormalGroup.ModuleLaw
