import Langlands.Geometry.FormalGroup.AtlasMorphism
import Langlands.Geometry.FormalGroup.GlobalAtlas
import Mathlib.CategoryTheory.Whiskering

/-! # Global formal maps induce atlas maps -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {P : ModuleLaw O R υ}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Restrict an actual global formal map using the proved chart comparisons. -/
def globalChartHom (f : ModuleLaw.Hom M N) (a : R) (A : CommAlgCat.{v} R)
    (ha : IsUnit (algebraMap R A a)) :
    ModuleLaw.Hom
      ((M.map (IsScalarTower.toAlgHom O R (Localization.Away a))).map
        (coefficientLift (O := O) a A ha))
      ((N.map (IsScalarTower.toAlgHom O R (Localization.Away a))).map
        (coefficientLift (O := O) a A ha)) :=
  (globalChartIso N a A ha).inv.comp
    ((f.map (IsScalarTower.toAlgHom O R A)).comp (globalChartIso M a A ha).hom)

/-- The chart map has exactly the original map's coefficient-extended series. -/
@[simp]
theorem globalChartHom_coordinates (f : ModuleLaw.Hom M N) (a : R)
    (A : CommAlgCat.{v} R) (ha : IsUnit (algebraMap R A a)) :
    (globalChartHom f a A ha).toHom.toCoordinateMap =
      f.toHom.toCoordinateMap.map (algebraMap R A) := by
  change CoordinateMap.id.comp
    ((f.toHom.toCoordinateMap.map (algebraMap R A)).comp CoordinateMap.id) = _
  rw [CoordinateMap.id_comp, CoordinateMap.comp_id]

/-- Global formal O-linear maps induce same-cover atlas morphisms. -/
def ofGlobalHom (f : ModuleLaw.Hom M N) (s : Set R) (hs : Ideal.span s = ⊤) :
    Hom (ofGlobalCover M s hs) (ofGlobalCover N s hs) rfl where
  hom A b hb := globalChartHom f b.val A hb
  natural φ b ha hb := by
    rw [globalChartHom_coordinates, globalChartHom_coordinates,
      CoordinateMap.map_ringHom_comp]
    exact congrArg (fun q : R →+* _ => f.toHom.toCoordinateMap.map q)
      (AlgHom.comp_algebraMap φ.hom)
  transition A b c hb hc := by
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change (CoordinateMap.id.comp CoordinateMap.id).comp
      (globalChartHom f b.val A hb).toHom.toCoordinateMap =
        (globalChartHom f c.val A hc).toHom.toCoordinateMap.comp
          (CoordinateMap.id.comp CoordinateMap.id)
    simp only [CoordinateMap.id_comp, CoordinateMap.comp_id, globalChartHom_coordinates]

@[simp]
theorem ofGlobalHom_id (M : ModuleLaw O R σ) (s : Set R) (hs : Ideal.span s = ⊤) :
    ofGlobalHom (ModuleLaw.Hom.id M) s hs = Hom.id (ofGlobalCover M s hs) := by
  apply Hom.ext
  intro A b hb
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  change (globalChartHom (ModuleLaw.Hom.id M) b.val A hb).toHom.toCoordinateMap =
    CoordinateMap.id
  rw [globalChartHom_coordinates]
  exact CoordinateMap.map_id _

@[simp]
theorem ofGlobalHom_comp (g : ModuleLaw.Hom N P) (f : ModuleLaw.Hom M N)
    (s : Set R) (hs : Ideal.span s = ⊤) :
    ofGlobalHom (g.comp f) s hs = (ofGlobalHom g s hs).comp (ofGlobalHom f s hs) := by
  apply Hom.ext
  intro A b hb
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  change (globalChartHom (g.comp f) b.val A hb).toHom.toCoordinateMap =
    (globalChartHom g b.val A hb).toHom.toCoordinateMap.comp
      (globalChartHom f b.val A hb).toHom.toCoordinateMap
  rw [globalChartHom_coordinates, globalChartHom_coordinates, globalChartHom_coordinates]
  exact CoordinateMap.map_comp _ _ _

/-- The singleton point comparison intertwines the original formal map. -/
theorem globalPointEquiv_ofGlobalHom (f : ModuleLaw.Hom M N)
    (A : CommAlgCat.{v} R) (x : (ofGlobal M).Point A) :
    globalPointEquiv N A ((ofGlobalHom f {1} (by simp)).onPoints A x) =
      f.onAlgebraPoints (globalPointEquiv M A x) := by
  have h1 : IsUnit (algebraMap R A (1 : R)) := by simp
  let y : SeriesPoint A σ Empty :=
    x.val ⟨A, 𝟙 A, oneChart M, oneChart_unit M A⟩
  change SeriesPoint.eval CoordinateMap.id
    (SeriesPoint.eval (globalChartHom f 1 A h1).toHom.toCoordinateMap y) =
    SeriesPoint.eval (f.toHom.toCoordinateMap.map (algebraMap R A))
      (SeriesPoint.eval CoordinateMap.id y)
  rw [SeriesPoint.eval_id, SeriesPoint.eval_id, globalChartHom_coordinates]

/-- The singleton functor comparison is also natural in global formal maps. -/
theorem globalPointFunctorIso_natural (f : ModuleLaw.Hom M N) :
    (ofGlobalHom f {1} (by simp)).pointNatTrans ≫ (globalPointFunctorIso N).hom =
      (globalPointFunctorIso M).hom ≫
        Functor.whiskerRight f.algebraPointNatTrans (ModuleCat.uliftFunctor.{v + 1, v} O) := by
  apply NatTrans.ext
  funext A
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ULift.up (globalPointEquiv N A ((ofGlobalHom f {1} (by simp)).onPoints A x)) =
    ULift.up (f.onAlgebraPoints (globalPointEquiv M A x))
  exact congrArg ULift.up (globalPointEquiv_ofGlobalHom f A x)

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
