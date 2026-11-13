import Langlands.Geometry.FormalGroup.AtlasBaseChange
import Langlands.Geometry.FormalGroup.SpecialAtlas

/-! # Coefficient extension of order actions and special formal atlases -/

noncomputable section

universe u v w s

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ : Type} [Finite σ]
variable {X : BasicAtlas O R σ} (E : OrderAction D X) (S : CommAlgCat.{v} R)

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Extend the actual order action to the new localization chart. -/
def baseOrderChart (b : X.baseOpens S) :
    ModuleLaw.OrderAction D (X.baseChart S b) :=
  (E.chart (X.baseSource S b)).map (X.baseChartCoefficient S b)

/-- The two coefficient routes give the same actual order endomorphism series. -/
theorem baseOrderChart_coordinates (A : CommAlgCat.{v} S) (b : X.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) (d : D) :
    (((E.baseOrderChart S b).map (coefficientLift (O := O) b.val A hb)).action d).toHom.toCoordinateMap =
      (((E.chart (X.baseSource S b)).map
        (coefficientLift (O := O) (X.baseSource S b).val (restrictTest S A)
          (X.baseSource_unit S A b hb))).action d).toHom.toCoordinateMap := by
  change (((E.chart (X.baseSource S b)).action d).toHom.toCoordinateMap.map
    (X.baseChartCoefficient S b).toRingHom).map
      (coefficientLift (O := O) b.val A hb).toRingHom = _
  rw [CoordinateMap.map_ringHom_comp, X.baseCoefficient_comp]
  rfl

/-- The coefficient chart comparison is an actual order-linear formal isomorphism. -/
def baseOrderChartIso (A : CommAlgCat.{v} S) (b : X.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) :
    ModuleLaw.OrderAction.Iso
      ((E.baseOrderChart S b).map (coefficientLift (O := O) b.val A hb))
      ((E.chart (X.baseSource S b)).map
        (coefficientLift (O := O) (X.baseSource S b).val (restrictTest S A)
          (X.baseSource_unit S A b hb))) where
  hom := ⟨(X.baseChartIso S A b hb).hom, by
    intro d
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change CoordinateMap.id.comp
      ((((E.baseOrderChart S b).map _).action d).toHom.toCoordinateMap) =
        ((((E.chart (X.baseSource S b)).map _).action d).toHom.toCoordinateMap).comp
          CoordinateMap.id
    rw [CoordinateMap.id_comp, CoordinateMap.comp_id, E.baseOrderChart_coordinates]⟩
  inv := ⟨(X.baseChartIso S A b hb).inv, by
    intro d
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change CoordinateMap.id.comp
      ((((E.chart (X.baseSource S b)).map _).action d).toHom.toCoordinateMap) =
        ((((E.baseOrderChart S b).map _).action d).toHom.toCoordinateMap).comp
          CoordinateMap.id
    rw [CoordinateMap.id_comp, CoordinateMap.comp_id, E.baseOrderChart_coordinates]⟩
  inv_hom := by
    apply Subtype.ext
    exact (X.baseChartIso S A b hb).inv_hom
  hom_inv := by
    apply Subtype.ext
    exact (X.baseChartIso S A b hb).hom_inv

/-- Extended order actions commute with the actual image-chart transitions. -/
theorem baseOrderTransition (A : CommAlgCat.{v} S) (a b : X.baseOpens S)
    (ha : IsUnit (algebraMap S A a.val)) (hb : IsUnit (algebraMap S A b.val))
    (d : D) :
    (X.baseTransition S A a b ha hb).hom.comp
      (((E.baseOrderChart S a).map (coefficientLift (O := O) a.val A ha)).action d) =
        (((E.baseOrderChart S b).map (coefficientLift (O := O) b.val A hb)).action d).comp
          (X.baseTransition S A a b ha hb).hom := by
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  change (X.baseTransition S A a b ha hb).hom.toHom.toCoordinateMap.comp
    ((((E.baseOrderChart S a).map _).action d).toHom.toCoordinateMap) =
      ((((E.baseOrderChart S b).map _).action d).toHom.toCoordinateMap).comp
        (X.baseTransition S A a b ha hb).hom.toHom.toCoordinateMap
  rw [X.baseTransition_coordinates, E.baseOrderChart_coordinates,
    E.baseOrderChart_coordinates]
  exact congrArg (fun f => f.toHom.toCoordinateMap)
    (E.transition (restrictTest S A) (X.baseSource S a) (X.baseSource S b)
      (X.baseSource_unit S A a ha) (X.baseSource_unit S A b hb) d)

/-- Coefficient extension of an atlas with its actual order action. -/
def baseChange : OrderAction D (X.baseChange S) where
  chart := E.baseOrderChart S
  transition := E.baseOrderTransition S

/-- The chart point comparison is linear for the full order action. -/
def baseChangeChartEquiv (A : CommAlgCat.{v} S) (b : X.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) :
    (E.baseChange S).ChartPoint A b hb ≃ₗ[D]
      E.ChartPoint (restrictTest S A) (X.baseSource S b) (X.baseSource_unit S A b hb) :=
  (E.baseOrderChartIso S A b hb).onPoints

@[simp]
theorem baseChangeChartEquiv_apply (A : CommAlgCat.{v} S) (b : X.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) (x : (E.baseChange S).ChartPoint A b hb) :
    E.baseChangeChartEquiv S A b hb x = x := by
  change SeriesPoint.eval CoordinateMap.id x = x
  exact SeriesPoint.eval_id x

@[simp]
theorem baseChangeChartEquiv_symm_apply (A : CommAlgCat.{v} S) (b : X.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val))
    (x : E.ChartPoint (restrictTest S A) (X.baseSource S b) (X.baseSource_unit S A b hb)) :
    (E.baseChangeChartEquiv S A b hb).symm x = x := by
  change SeriesPoint.eval CoordinateMap.id x = x
  exact SeriesPoint.eval_id x

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

namespace Langlands.FormalGroup.LocalDivision.SpecialAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable (X : SpecialAtlas K D ι R) (S : CommAlgCat.{v} R)

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Extend actual special chart laws and their full division-order action. -/
def baseChange : SpecialAtlas K D ι S where
  atlas := X.atlas.baseChange S
  order := X.order.baseChange S
  unramified := X.unramified
  tangent b := (X.tangent (X.atlas.baseSource S b)).map (X.atlas.baseChartCoefficient S b)

/-- Coefficient extension preserves actual scalar-kernel height d² and base nilpotence. -/
theorem baseChange_height {π : 𝒪[K]} (h : X.HasHeightSquared π) :
    (X.baseChange S).HasHeightSquared π := by
  refine ⟨h.1, ?_, fun b => (h.2.2 (X.atlas.baseSource S b)).map
    (X.atlas.baseChartCoefficient S b)⟩
  change IsNilpotent (algebraMap R S (algebraMap 𝒪[K] R π))
  exact h.2.1.map (algebraMap R S)

/-- The new special chart has the original chosen chart's order-module points. -/
def baseChangeChartEquiv (A : CommAlgCat.{v} S) (b : X.atlas.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) :
    (X.baseChange S).order.ChartPoint A b hb ≃ₗ[IntegerRing K D]
      X.order.ChartPoint (BasicAtlas.restrictTest S A) (X.atlas.baseSource S b)
        (X.atlas.baseSource_unit S A b hb) :=
  X.order.baseChangeChartEquiv S A b hb

end Langlands.FormalGroup.LocalDivision.SpecialAtlas
