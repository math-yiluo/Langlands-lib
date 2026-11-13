import Langlands.Geometry.FormalGroup.BasicAtlas
import Mathlib.Algebra.Category.ModuleCat.Ulift

/-! # Coordinate atlases induced by a global formal module -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ : Type} [Finite σ]

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- The original structural coefficients are recovered after localization. -/
theorem globalCoefficient_comp (a : R) (A : CommAlgCat.{v} R)
    (ha : IsUnit (algebraMap R A a)) :
    (coefficientLift (O := O) a A ha).toRingHom.comp
      (algebraMap R (Localization.Away a)) = algebraMap R A := by
  ext r
  exact coefficientLift_algebraMap a A ha r

/-- Restricting to a principal open and then extending recovers the global law. -/
def globalChartIso (M : ModuleLaw O R σ) (a : R) (A : CommAlgCat.{v} R)
    (ha : IsUnit (algebraMap R A a)) :
    Iso ((M.map (IsScalarTower.toAlgHom O R (Localization.Away a))).map
      (coefficientLift (O := O) a A ha)) (M.map (IsScalarTower.toAlgHom O R A)) :=
  Iso.ofIdenticalCoordinates
    (by
      change (M.groupLaw.addition.map (algebraMap R (Localization.Away a))).map
        (coefficientLift (O := O) a A ha).toRingHom =
          M.groupLaw.addition.map (algebraMap R A)
      rw [CoordinateMap.map_ringHom_comp, globalCoefficient_comp])
    (fun c => by
      change ((M.action c).toCoordinateMap.map (algebraMap R (Localization.Away a))).map
        (coefficientLift (O := O) a A ha).toRingHom =
          (M.action c).toCoordinateMap.map (algebraMap R A)
      rw [CoordinateMap.map_ringHom_comp, globalCoefficient_comp])

/-- Global laws supply actual identity-coordinate transition isomorphisms. -/
def globalTransition (M : ModuleLaw O R σ) (A : CommAlgCat.{v} R) (a b : R)
    (ha : IsUnit (algebraMap R A a)) (hb : IsUnit (algebraMap R A b)) :
    Iso ((M.map (IsScalarTower.toAlgHom O R (Localization.Away a))).map
      (coefficientLift (O := O) a A ha))
      ((M.map (IsScalarTower.toAlgHom O R (Localization.Away b))).map
        (coefficientLift (O := O) b A hb)) :=
  (globalChartIso M a A ha).trans (globalChartIso M b A hb).symm

/-- Any principal-open cover restricts an actual global formal O-module. -/
def ofGlobalCover (M : ModuleLaw O R σ) (s : Set R) (hs : Ideal.span s = ⊤) :
    BasicAtlas O R σ where
  opens := s
  covers := hs
  chart a := M.map (IsScalarTower.toAlgHom O R (Localization.Away a.val))
  transition A a b ha hb := globalTransition M A a.val b.val ha hb
  transition_self A a ha := by
    apply Iso.ext_hom
    apply Hom.ext
    apply CommLaw.Hom.ext
    exact CoordinateMap.id_comp _
  transition_cocycle A a b c ha hb hc := by
    apply Iso.ext_hom
    apply Hom.ext
    apply CommLaw.Hom.ext
    change (CoordinateMap.id.comp CoordinateMap.id).comp
      (CoordinateMap.id.comp CoordinateMap.id) = CoordinateMap.id.comp CoordinateMap.id
    simp only [CoordinateMap.id_comp]
  transition_natural φ a b ha hb ha' hb' := by
    change (CoordinateMap.id.comp CoordinateMap.id).map φ.hom.toRingHom =
      CoordinateMap.id.comp CoordinateMap.id
    simp only [CoordinateMap.id_comp, CoordinateMap.map_id]

/-- The one-chart atlas of a global formal module. -/
def ofGlobal (M : ModuleLaw O R σ) : BasicAtlas O R σ :=
  ofGlobalCover M {1} (by simp)

/-- The distinguished everywhere-defined chart in the singleton atlas. -/
def oneChart (M : ModuleLaw O R σ) : (ofGlobal M).opens := ⟨1, by simp [ofGlobal, ofGlobalCover]⟩

theorem oneChart_unit (M : ModuleLaw O R σ) (A : CommAlgCat.{v} R) :
    IsUnit (algebraMap R A (oneChart M).val) := by
  change IsUnit (algebraMap R A (1 : R))
  simp

/-- The singleton atlas has exactly the original nilpotent module points. -/
def globalPointEquiv (M : ModuleLaw O R σ) (A : CommAlgCat.{v} R) :
    (ofGlobal M).Point A ≃ₗ[O] M.AlgebraPoint A :=
  ((ofGlobal M).chartEquiv (oneChart M) (oneChart_unit M A)).trans
    (globalChartIso M 1 A (oneChart_unit M A)).onPoints

@[simp]
theorem globalPointEquiv_apply (M : ModuleLaw O R σ) (A : CommAlgCat.{v} R)
    (x : (ofGlobal M).Point A) :
    globalPointEquiv M A x = x.val ⟨A, 𝟙 A, oneChart M, oneChart_unit M A⟩ := by
  change SeriesPoint.eval CoordinateMap.id _ = _
  exact SeriesPoint.eval_id _

/-- This point comparison commutes with every coefficient algebra map. -/
theorem globalPointEquiv_natural (M : ModuleLaw O R σ)
    {A B : CommAlgCat.{v} R} (φ : A ⟶ B) (x : (ofGlobal M).Point A) :
    globalPointEquiv M B ((ofGlobal M).mapPoints φ x) =
      M.algebraMapPoints φ.hom (globalPointEquiv M A x) := by
  simp only [globalPointEquiv_apply]
  change x.val ⟨B, φ ≫ 𝟙 B, oneChart M, oneChart_unit M B⟩ =
    SeriesPoint.map φ.hom.toRingHom
      (x.val ⟨A, 𝟙 A, oneChart M, oneChart_unit M A⟩)
  have h := x.property.1 A B (𝟙 A) φ (oneChart M)
    (oneChart_unit M A) (oneChart_unit M B)
  rw [Category.id_comp, pointMap_apply] at h
  rw [Category.comp_id]
  exact h.symm

/-- A natural isomorphism to the original point functor after universe lifting. -/
def globalPointFunctorIso (M : ModuleLaw O R σ) :
    (ofGlobal M).pointFunctor ≅
      M.algebraPointFunctor ⋙ ModuleCat.uliftFunctor.{v + 1, v} O :=
  NatIso.ofComponents
    (fun A => ((globalPointEquiv M A).trans ULift.moduleEquiv.symm).toModuleIso)
    (by
      intro A B φ
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change ULift.up (globalPointEquiv M B ((ofGlobal M).mapPoints φ x)) =
        ULift.up (M.algebraMapPoints φ.hom (globalPointEquiv M A x))
      exact congrArg ULift.up (globalPointEquiv_natural M φ x))

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
