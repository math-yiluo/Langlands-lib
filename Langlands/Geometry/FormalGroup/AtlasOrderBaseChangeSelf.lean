import Langlands.Geometry.FormalGroup.AtlasBaseChangeSelf
import Langlands.Geometry.FormalGroup.AtlasOrderBaseChangeAlong

/-! # Full-order formal comparison for identity coefficient extension -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ : Type} [Finite σ]
variable {X : BasicAtlas O R σ} (E : OrderAction D X)

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Identity extension retains the entire original action series for each order element. -/
theorem baseIdOrderChart_coordinates (A : CommAlgCat.{v} R) (b : X.opens)
    (hb : IsUnit (algebraMap R A b.val)) (d : D) :
    ((((E.baseChangeAlong (AlgHom.id O R)).chart
      (sourceChart X.baseIdOpens_eq b)).map
        (coefficientLift (O := O) b.val A hb)).action d).toHom.toCoordinateMap =
      (((E.chart b).map (coefficientLift (O := O) b.val A hb)).action d).toHom.toCoordinateMap := by
  refine (E.baseChangeAlongOrderChart_coordinates (AlgHom.id O R) A
    (sourceChart X.baseIdOpens_eq b) hb d).trans ?_
  have hn := (E.endomorphism d).natural (identityTestHom (O := O) A)
    (X.baseIdSource b)
    (X.baseSource_unit (coefficientTest (AlgHom.id O R)) A _ hb)
    (X.baseIdSource_unit A b hb)
  change (((E.chart (X.baseIdSource b)).map
    (coefficientLift (O := O) (X.baseIdSource b).val
      (restrictCoefficientAlgebra (AlgHom.id O R) A) _)).action d).toHom.toCoordinateMap.map
        (RingHom.id A) = _ at hn
  exact (CoordinateMap.map_ringHom_id _).symm.trans
    (hn.trans (E.testOrderChart_coordinates_eq A _ b _ hb (X.baseIdSource_eq b) d))

/-- The actual identity-extension formal map commutes with the entire acting order. -/
def baseIdHom :
    Hom (E.baseChangeAlong (AlgHom.id O R)) E X.baseIdOpens_eq :=
  ⟨X.baseIdHom, by
    intro A b hb d
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change CoordinateMap.id.comp
      ((((E.baseChangeAlong (AlgHom.id O R)).chart
        (sourceChart X.baseIdOpens_eq b)).map
          (coefficientLift (O := O) b.val A hb)).action d).toHom.toCoordinateMap =
      (((E.chart b).map
        (coefficientLift (O := O) b.val A hb)).action d).toHom.toCoordinateMap.comp CoordinateMap.id
    rw [CoordinateMap.id_comp, CoordinateMap.comp_id, E.baseIdOrderChart_coordinates]⟩

/-- Forgetting the order retains exactly the original forward formal map. -/
@[simp]
theorem baseIdHom_val : E.baseIdHom.val = X.baseIdHom := rfl

/-- The actual reverse identity-extension formal map also commutes with the entire order. -/
def baseIdInv :
    Hom E (E.baseChangeAlong (AlgHom.id O R)) X.baseIdOpens_eq.symm :=
  ⟨X.baseIdInv, by
    intro A b hb d
    let b' := sourceChart X.baseIdOpens_eq.symm b
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change CoordinateMap.id.comp
      (((E.chart b').map
        (coefficientLift (O := O) b'.val A hb)).action d).toHom.toCoordinateMap =
      ((((E.baseChangeAlong (AlgHom.id O R)).chart
        (sourceChart X.baseIdOpens_eq b')).map
          (coefficientLift (O := O) b'.val A hb)).action d).toHom.toCoordinateMap.comp CoordinateMap.id
    rw [CoordinateMap.id_comp, CoordinateMap.comp_id, E.baseIdOrderChart_coordinates]⟩

/-- Forgetting the order retains exactly the original reverse formal map. -/
@[simp]
theorem baseIdInv_val : E.baseIdInv.val = X.baseIdInv := rfl

/-- Identity coefficient extension compares by actual inverse full-order formal maps. -/
def baseIdIso :
    Iso (E.baseChangeAlong (AlgHom.id O R)) E X.baseIdOpens_eq where
  hom := E.baseIdHom
  inv := E.baseIdInv
  inv_hom := by
    apply Subtype.ext
    exact X.baseIdIso.inv_hom
  hom_inv := by
    apply Subtype.ext
    exact X.baseIdIso.hom_inv

/-- The full-order formal comparison realizes identity restriction on entire families. -/
theorem baseId_onPoints (A : CommAlgCat.{v} R)
    (x : E.Point (restrictCoefficientAlgebra (AlgHom.id O R) A)) :
    E.baseIdIso.onPoints A (E.baseChangeAlongPointEquiv (AlgHom.id O R) A x) =
      E.mapPoints (identityTestHom (O := O) A) x := by
  change X.baseIdIso.onPoints A (E.baseChangeAlongPointEquiv (AlgHom.id O R) A x) =
    X.mapPoints (identityTestHom (O := O) A) x
  rw [E.baseChangeAlongPointEquiv_eq]
  exact X.baseId_onPoints A x

/-- The inverse full-order formal comparison realizes the reverse entire-family square. -/
theorem baseId_inv_onPoints (A : CommAlgCat.{v} R)
    (x : E.Point (restrictCoefficientAlgebra (AlgHom.id O R) A)) :
    (E.baseIdIso.onPoints A).symm (E.mapPoints (identityTestHom (O := O) A) x) =
      E.baseChangeAlongPointEquiv (AlgHom.id O R) A x :=
  (LinearEquiv.symm_apply_eq (E.baseIdIso.onPoints A)).mpr
    (E.baseId_onPoints A x).symm

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction
