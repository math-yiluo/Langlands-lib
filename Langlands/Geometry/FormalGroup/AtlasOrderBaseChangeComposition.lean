import Langlands.Geometry.FormalGroup.AtlasBaseChangeComposition
import Langlands.Geometry.FormalGroup.AtlasOrderBaseChangeMorphism

/-! # Successive coefficient extensions with the full acting order -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ : Type} [Finite σ]
variable {X : BasicAtlas O R σ} (E : OrderAction D X)
variable (S : CommAlgCat.{v} R) (T : CommAlgCat.{v} S)

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- The successive order action has the series of its iterated original source. -/
theorem baseCompLeftOrderChart_coordinates (A : CommAlgCat.{v} T)
    (b : X.baseOpens (restrictTest S T))
    (hb : IsUnit (algebraMap T A b.val)) (d : D) :
    (((((E.baseChange S).baseOrderChart T
      (sourceChart (X.baseCompOpens_eq S T) b)).map
        (coefficientLift (O := O) b.val A hb))).action d).toHom.toCoordinateMap =
      (((E.chart (X.baseCompIterSource S T b)).map
        (coefficientLift (O := O) (X.baseCompIterSource S T b).val
          (restrictTest (restrictTest S T) A) (X.baseCompIter_unit S T A b hb))).action d).toHom.toCoordinateMap :=
  ((E.baseChange S).baseOrderChart_coordinates T A _ hb d).trans
    (E.baseOrderChart_coordinates S (restrictTest T A) _ _ d)

/-- The actual successive-coefficient formal map commutes with every order element. -/
def baseCompHom :
    Hom ((E.baseChange S).baseChange T) (E.baseChange (restrictTest S T))
      (X.baseCompOpens_eq S T) :=
  ⟨X.baseCompHom S T, by
    intro A b hb d
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change (X.baseCompChartIso S T A b hb).hom.toHom.toCoordinateMap.comp
      (((((E.baseChange S).baseOrderChart T
        (sourceChart (X.baseCompOpens_eq S T) b)).map
          (coefficientLift (O := O) b.val A hb))).action d).toHom.toCoordinateMap =
      ((((E.baseOrderChart (restrictTest S T) b).map
        (coefficientLift (O := O) b.val A hb))).action d).toHom.toCoordinateMap.comp
          (X.baseCompChartIso S T A b hb).hom.toHom.toCoordinateMap
    exact (congrArg₂ (fun F G : CoordinateMap A σ σ => F.comp G)
      (X.baseCompChartIso_coordinates S T A b hb)
      (E.baseCompLeftOrderChart_coordinates S T A b hb d)).trans
      ((congrArg (fun f => f.toHom.toCoordinateMap)
        (E.transition (restrictTest (restrictTest S T) A)
          (X.baseCompIterSource S T b) (X.baseSource (restrictTest S T) b)
          (X.baseCompIter_unit S T A b hb)
          (X.baseSource_unit (restrictTest S T) A b hb) d)).trans
        (congrArg₂ (fun F G : CoordinateMap A σ σ => F.comp G)
          (E.baseOrderChart_coordinates (restrictTest S T) A b hb d)
          (X.baseCompChartIso_coordinates S T A b hb)).symm)⟩

/-- Forgetting the order retains exactly the original forward formal map. -/
@[simp]
theorem baseCompHom_val :
    (E.baseCompHom S T).val = X.baseCompHom S T := rfl

/-- The reverse formal map also commutes with the entire acting order. -/
def baseCompInv :
    Hom (E.baseChange (restrictTest S T)) ((E.baseChange S).baseChange T)
      (X.baseCompOpens_eq S T).symm :=
  ⟨X.baseCompInv S T, by
    intro A b hb d
    let b' := sourceChart (X.baseCompOpens_eq S T).symm b
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change (X.baseCompInvChartIso S T A b' hb).hom.toHom.toCoordinateMap.comp
      ((((E.baseOrderChart (restrictTest S T) b').map
        (coefficientLift (O := O) b'.val A hb))).action d).toHom.toCoordinateMap =
      (((((E.baseChange S).baseOrderChart T
        (sourceChart (X.baseCompOpens_eq S T) b')).map
          (coefficientLift (O := O) b'.val A hb))).action d).toHom.toCoordinateMap.comp
            (X.baseCompInvChartIso S T A b' hb).hom.toHom.toCoordinateMap
    exact (congrArg₂ (fun F G : CoordinateMap A σ σ => F.comp G)
      (X.baseCompInvChartIso_coordinates S T A b' hb)
      (E.baseOrderChart_coordinates (restrictTest S T) A b' hb d)).trans
      ((congrArg (fun f => f.toHom.toCoordinateMap)
        (E.transition (restrictTest (restrictTest S T) A)
          (X.baseSource (restrictTest S T) b') (X.baseCompIterSource S T b')
          (X.baseSource_unit (restrictTest S T) A b' hb)
          (X.baseCompIter_unit S T A b' hb) d)).trans
        (congrArg₂ (fun F G : CoordinateMap A σ σ => F.comp G)
          (E.baseCompLeftOrderChart_coordinates S T A b' hb d)
          (X.baseCompInvChartIso_coordinates S T A b' hb)).symm)⟩

/-- Forgetting the order retains exactly the original reverse formal map. -/
@[simp]
theorem baseCompInv_val :
    (E.baseCompInv S T).val = X.baseCompInv S T := rfl

/-- Successive coefficient extensions compare by actual order-linear formal maps. -/
def baseCompIso :
    Iso ((E.baseChange S).baseChange T) (E.baseChange (restrictTest S T))
      (X.baseCompOpens_eq S T) where
  hom := E.baseCompHom S T
  inv := E.baseCompInv S T
  inv_hom := by
    apply Subtype.ext
    exact (X.baseCompIso S T).inv_hom
  hom_inv := by
    apply Subtype.ext
    exact (X.baseCompIso S T).hom_inv

/-- The order-linear formal comparison realizes the complete-family square. -/
theorem baseComp_onPoints (A : CommAlgCat.{v} T)
    (x : E.Point (restrictTest (restrictTest S T) A)) :
    (E.baseCompIso S T).onPoints A
      ((E.baseChange S).toBaseChangePoints T A
        (E.toBaseChangePoints S (restrictTest T A) x)) =
      E.toBaseChangePoints (restrictTest S T) A x :=
  X.baseComp_onPoints S T A x

/-- The inverse order-linear formal comparison realizes the reverse family square. -/
theorem baseComp_inv_onPoints (A : CommAlgCat.{v} T)
    (x : E.Point (restrictTest (restrictTest S T) A)) :
    ((E.baseCompIso S T).onPoints A).symm
      (E.toBaseChangePoints (restrictTest S T) A x) =
      (E.baseChange S).toBaseChangePoints T A
        (E.toBaseChangePoints S (restrictTest T A) x) :=
  X.baseComp_inv_onPoints S T A x

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction
