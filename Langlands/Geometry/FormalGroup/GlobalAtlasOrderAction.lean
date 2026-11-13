import Langlands.Geometry.FormalGroup.AtlasOrderAction
import Langlands.Geometry.FormalGroup.GlobalAtlas
import Mathlib.CategoryTheory.Whiskering

/-! # Global order actions and their formal coordinate atlases -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ : Type} [Finite σ]
variable {M : ModuleLaw O R σ}

attribute [local instance] coefficientAlgebra coefficientScalarTower

namespace OrderAction

variable (E : OrderAction D M)

/-- Nilpotent algebra points with the evaluated full order action. -/
abbrev AlgebraPoint (A : CommAlgCat.{v} R) :=
  (E.map (IsScalarTower.toAlgHom O R A)).Point Empty

/-- The original coefficient map is linear for the full order action. -/
def algebraMapPoints {A B : CommAlgCat.{v} R} (φ : A ⟶ B) :
    E.AlgebraPoint A →ₗ[D] E.AlgebraPoint B where
  toFun := M.algebraMapPoints φ.hom
  map_add' := (M.algebraMapPoints φ.hom).map_add
  map_smul' a x := (E.action a).onAlgebraPoints_natural φ.hom x

/-- The actual order-module point functor of a globally coordinated law. -/
def algebraPointFunctor : CommAlgCat.{v} R ⥤ ModuleCat.{v} D where
  obj A := ModuleCat.of D (E.AlgebraPoint A)
  map φ := ModuleCat.ofHom (E.algebraMapPoints φ)
  map_id A := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact M.algebraMapPoints_id x
  map_comp φ ψ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact M.algebraMapPoints_comp φ.hom ψ.hom x

/-- Restrict the order-module point functor to nilpotent coefficient algebras. -/
def nilpAlgebraPointFunctor (π : R) : Nilp.{v, v} R π ⥤ ModuleCat.{v} D :=
  Nilp.forget R π ⋙ E.algebraPointFunctor

end OrderAction

namespace BasicAtlas

variable (E : ModuleLaw.OrderAction D M)

/-- The twice extended formal endomorphism has the original extended coordinates. -/
theorem globalOrderChart_coordinates (a : R) (A : CommAlgCat.{v} R)
    (ha : IsUnit (algebraMap R A a)) (d : D) :
    (((E.map (IsScalarTower.toAlgHom O R (Localization.Away a))).map
      (coefficientLift (O := O) a A ha)).action d).toHom.toCoordinateMap =
        (E.action d).toHom.toCoordinateMap.map (algebraMap R A) := by
  change ((E.action d).toHom.toCoordinateMap.map
    (algebraMap R (Localization.Away a))).map
      (coefficientLift (O := O) a A ha).toRingHom = _
  rw [CoordinateMap.map_ringHom_comp, globalCoefficient_comp]

/-- The global chart comparison is an actual order-linear formal isomorphism. -/
def globalOrderChartIso (a : R) (A : CommAlgCat.{v} R)
    (ha : IsUnit (algebraMap R A a)) :
    ModuleLaw.OrderAction.Iso
      ((E.map (IsScalarTower.toAlgHom O R (Localization.Away a))).map
        (coefficientLift (O := O) a A ha))
      (E.map (IsScalarTower.toAlgHom O R A)) where
  hom := ⟨(globalChartIso M a A ha).hom, by
    intro d
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change CoordinateMap.id.comp
      ((((E.map _).map _).action d).toHom.toCoordinateMap) =
        ((E.action d).toHom.toCoordinateMap.map (algebraMap R A)).comp CoordinateMap.id
    rw [CoordinateMap.id_comp, CoordinateMap.comp_id, globalOrderChart_coordinates]⟩
  inv := ⟨(globalChartIso M a A ha).inv, by
    intro d
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change CoordinateMap.id.comp
      ((E.action d).toHom.toCoordinateMap.map (algebraMap R A)) =
        ((((E.map _).map _).action d).toHom.toCoordinateMap).comp CoordinateMap.id
    rw [CoordinateMap.id_comp, CoordinateMap.comp_id, globalOrderChart_coordinates]⟩
  inv_hom := by
    apply Subtype.ext
    exact (globalChartIso M a A ha).inv_hom
  hom_inv := by
    apply Subtype.ext
    exact (globalChartIso M a A ha).hom_inv

/-- Restrict an actual global order action to any principal-open cover. -/
def ofGlobalCoverOrderAction (s : Set R) (hs : Ideal.span s = ⊤) :
    OrderAction D (ofGlobalCover M s hs) where
  chart b := E.map (IsScalarTower.toAlgHom O R (Localization.Away b.val))
  transition A b c hb hc d := by
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change (CoordinateMap.id.comp CoordinateMap.id).comp
      ((((E.map _).map _).action d).toHom.toCoordinateMap) =
        ((((E.map _).map _).action d).toHom.toCoordinateMap).comp
          (CoordinateMap.id.comp CoordinateMap.id)
    simp only [CoordinateMap.id_comp, CoordinateMap.comp_id, globalOrderChart_coordinates]

/-- The singleton atlas with its restricted global order action. -/
def ofGlobalOrderAction : OrderAction D (ofGlobal M) :=
  ofGlobalCoverOrderAction E {1} (by simp)

/-- The singleton comparison respects the full order action. -/
def globalOrderPointEquiv (A : CommAlgCat.{v} R) :
    (ofGlobalOrderAction E).Point A ≃ₗ[D] E.AlgebraPoint A :=
  ((ofGlobalOrderAction E).chartEquiv (oneChart M) (oneChart_unit M A)).trans
    (globalOrderChartIso E 1 A (oneChart_unit M A)).onPoints

@[simp]
theorem globalOrderPointEquiv_apply (A : CommAlgCat.{v} R)
    (x : (ofGlobalOrderAction E).Point A) :
    globalOrderPointEquiv E A x =
      x.val ⟨A, 𝟙 A, oneChart M, oneChart_unit M A⟩ := by
  change SeriesPoint.eval CoordinateMap.id _ = _
  exact SeriesPoint.eval_id _

/-- Forgetting the order recovers the original singleton comparison. -/
theorem globalOrderPointEquiv_eq (A : CommAlgCat.{v} R)
    (x : (ofGlobalOrderAction E).Point A) :
    globalOrderPointEquiv E A x = globalPointEquiv M A x := by
  exact (globalOrderPointEquiv_apply E A x).trans (globalPointEquiv_apply M A x).symm

/-- The order-linear singleton comparison commutes with coefficient extension. -/
theorem globalOrderPointEquiv_natural {A B : CommAlgCat.{v} R} (φ : A ⟶ B)
    (x : (ofGlobalOrderAction E).Point A) :
    globalOrderPointEquiv E B ((ofGlobalOrderAction E).mapPoints φ x) =
      E.algebraMapPoints φ (globalOrderPointEquiv E A x) := by
  exact globalPointEquiv_natural M φ x

/-- The singleton order-module functor is the original one after universe lifting. -/
def globalOrderPointFunctorIso :
    (ofGlobalOrderAction E).pointFunctor ≅
      E.algebraPointFunctor ⋙ ModuleCat.uliftFunctor.{v + 1, v} D :=
  NatIso.ofComponents
    (fun A => ((globalOrderPointEquiv E A).trans ULift.moduleEquiv.symm).toModuleIso)
    (by
      intro A B φ
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change ULift.up (globalOrderPointEquiv E B ((ofGlobalOrderAction E).mapPoints φ x)) =
        ULift.up (E.algebraMapPoints φ (globalOrderPointEquiv E A x))
      exact congrArg ULift.up (globalOrderPointEquiv_natural E φ x))

/-- The same order-linear comparison restricted to Nilp. -/
def globalOrderNilpPointFunctorIso (π : R) :
    (ofGlobalOrderAction E).nilpPointFunctor π ≅
      E.nilpAlgebraPointFunctor π ⋙ ModuleCat.uliftFunctor.{v + 1, v} D :=
  Functor.isoWhiskerLeft (Nilp.forget R π) (globalOrderPointFunctorIso E)

end BasicAtlas

end Langlands.FormalGroup.ModuleLaw
