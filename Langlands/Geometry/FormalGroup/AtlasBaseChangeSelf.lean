import Langlands.Geometry.FormalGroup.AtlasBaseChangeAlong

/-! # Actual formal comparison for identity coefficient extension -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ : Type} [Finite σ]

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable (X : BasicAtlas O R σ)

/-- Identity coefficient extension retains the original principal generators. -/
theorem baseIdOpens_eq :
    (X.baseChangeAlong (AlgHom.id O R)).opens = X.opens := by
  change (fun r : R => r) '' X.opens = X.opens
  exact Set.image_id _

/-- The original chart selected above the identity image cover. -/
abbrev baseIdSource (b : X.opens) : X.opens :=
  X.baseSource (coefficientTest (AlgHom.id O R)) (sourceChart X.baseIdOpens_eq b)

/-- Identity extension selects the same generator as the original chart. -/
theorem baseIdSource_eq (b : X.opens) : X.baseIdSource b = b :=
  Subtype.ext (X.baseSource_image (coefficientTest (AlgHom.id O R)) _)

/-- Its generator is a unit on the original test. -/
theorem baseIdSource_unit (A : CommAlgCat.{v} R) (b : X.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    IsUnit (algebraMap R A (X.baseIdSource b).val) := by
  rw [X.baseIdSource_eq]
  exact hb

/-- Forget scalar linearity while inferring both scalar structures from the given map. -/
private def underlyingRingHom {C D : Type v} [CommRing C] [CommRing D]
    (α : Algebra O C) (β : Algebra O D) (f : @AlgHom O C D _ _ _ α β) : C →+* D :=
  @AlgHom.toRingHom O C D _ _ _ α β f

/-- The underlying ring map between the identity-extension localizations. -/
def baseIdChartRingHom (b : X.opens) :
    Localization.Away (X.baseIdSource b).val →+* Localization.Away b.val :=
  underlyingRingHom _ _
    (X.baseChartCoefficient (coefficientTest (AlgHom.id O R))
      (sourceChart X.baseIdOpens_eq b))

/-- This ring map retains every coefficient from the original base. -/
theorem baseIdChartRingHom_algebraMap (b : X.opens) (r : R) :
    X.baseIdChartRingHom b (algebraMap R (Localization.Away (X.baseIdSource b).val) r) =
      algebraMap R (Localization.Away b.val) r :=
  X.baseChartCoefficient_algebraMap (coefficientTest (AlgHom.id O R))
    (sourceChart X.baseIdOpens_eq b) r

/-- The two actual localization maps to the original test are equal. -/
theorem baseIdCoefficient_comp (A : CommAlgCat.{v} R) (b : X.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    (coefficientLift (O := O) b.val A hb).toRingHom.comp
        (X.baseIdChartRingHom b) =
      (coefficientLift (O := O) (X.baseIdSource b).val A
        (X.baseIdSource_unit A b hb)).toRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (X.baseIdSource b).val)
  ext r
  change coefficientLift (O := O) b.val A hb
      (X.baseIdChartRingHom b
        (algebraMap R (Localization.Away (X.baseIdSource b).val) r)) =
    coefficientLift (O := O) (X.baseIdSource b).val A (X.baseIdSource_unit A b hb)
      (algebraMap R (Localization.Away (X.baseIdSource b).val) r)
  rw [X.baseIdChartRingHom_algebraMap, coefficientLift_algebraMap,
    coefficientLift_algebraMap]

/-- Identity coordinates compare the extended chart with its original chart. -/
def baseIdChartIso (A : CommAlgCat.{v} R) (b : X.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    ModuleLaw.Iso
      (((X.baseChangeAlong (AlgHom.id O R)).chart
        (sourceChart X.baseIdOpens_eq b)).map (coefficientLift (O := O) b.val A hb))
      ((X.chart b).map (coefficientLift (O := O) b.val A hb)) :=
  ModuleLaw.Iso.ofIdenticalCoordinates
    (by
      change ((X.chart (X.baseIdSource b)).groupLaw.addition.map
        (X.baseIdChartRingHom b)).map
        (coefficientLift (O := O) b.val A hb).toRingHom = _
      rw [CoordinateMap.map_ringHom_comp, X.baseIdCoefficient_comp]
      exact congrArg (fun M : ModuleLaw O A σ => M.groupLaw.addition)
        (X.testChart_eq A _ _ _ hb (X.baseIdSource_eq b)))
    (fun c => by
      change (((X.chart (X.baseIdSource b)).action c).toCoordinateMap.map
        (X.baseIdChartRingHom b)).map
        (coefficientLift (O := O) b.val A hb).toRingHom = _
      rw [CoordinateMap.map_ringHom_comp, X.baseIdCoefficient_comp]
      exact congrArg (fun M : ModuleLaw O A σ => (M.action c).toCoordinateMap)
        (X.testChart_eq A _ _ _ hb (X.baseIdSource_eq b)))

/-- The identity ring map identifies an identity-restricted test with the original. -/
def identityTestHom (A : CommAlgCat.{v} R) :
    restrictCoefficientAlgebra (AlgHom.id O R) A ⟶ A :=
  CommAlgCat.ofHom { toRingHom := RingHom.id A, commutes' _ := rfl }

/-- The inverse identity ring map restores the identity-restricted test. -/
def identityTestInv (A : CommAlgCat.{v} R) :
    A ⟶ restrictCoefficientAlgebra (AlgHom.id O R) A :=
  CommAlgCat.ofHom { toRingHom := RingHom.id A, commutes' _ := rfl }

/-- Identity extension retains the full original transition series. -/
theorem baseIdTransition_coordinates (A : CommAlgCat.{v} R) (a b : X.opens)
    (ha : IsUnit (algebraMap R A a.val)) (hb : IsUnit (algebraMap R A b.val)) :
    ((X.baseChangeAlong (AlgHom.id O R)).transition A
      (sourceChart X.baseIdOpens_eq a) (sourceChart X.baseIdOpens_eq b) ha hb).hom.toHom.toCoordinateMap =
      (X.transition A a b ha hb).hom.toHom.toCoordinateMap := by
  refine ((X.baseChange (coefficientTest (AlgHom.id O R))).reAlgebra_transition_coordinates _
    (coefficientAlgebraAlong_eq (AlgHom.id O R)) A _ _ ha hb).trans ?_
  refine (X.baseTransition_coordinates (coefficientTest (AlgHom.id O R)) A _ _ ha hb).trans ?_
  have hn := X.transition_natural (identityTestHom (O := O) A)
    (X.baseIdSource a) (X.baseIdSource b)
    (X.baseSource_unit (coefficientTest (AlgHom.id O R)) A _ ha)
    (X.baseSource_unit (coefficientTest (AlgHom.id O R)) A _ hb)
    (X.baseIdSource_unit A a ha) (X.baseIdSource_unit A b hb)
  change (X.transition (restrictCoefficientAlgebra (AlgHom.id O R) A)
    (X.baseIdSource a) (X.baseIdSource b) _ _).hom.toHom.toCoordinateMap.map
      (RingHom.id A) = _ at hn
  exact (CoordinateMap.map_ringHom_id _).symm.trans
    (hn.trans (X.testTransition_coordinates_eq A _ _ a b _ _ ha hb
      (X.baseIdSource_eq a) (X.baseIdSource_eq b)))

/-- The identity extension maps formally to the original atlas by identity coordinates. -/
def baseIdHom : Hom (X.baseChangeAlong (AlgHom.id O R)) X X.baseIdOpens_eq where
  hom A b hb := (X.baseIdChartIso A b hb).hom
  natural φ b ha hb := by
    change CoordinateMap.id.map φ.hom.toRingHom = CoordinateMap.id
    exact CoordinateMap.map_id _
  transition A b c hb hc := by
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change (X.transition A b c hb hc).hom.toHom.toCoordinateMap.comp CoordinateMap.id =
      CoordinateMap.id.comp
        ((X.baseChangeAlong (AlgHom.id O R)).transition A
          (sourceChart X.baseIdOpens_eq b) (sourceChart X.baseIdOpens_eq c) hb hc).hom.toHom.toCoordinateMap
    rw [CoordinateMap.comp_id, CoordinateMap.id_comp, X.baseIdTransition_coordinates]

/-- The reverse formal comparison also uses identity coordinates on every test. -/
def baseIdInv : Hom X (X.baseChangeAlong (AlgHom.id O R)) X.baseIdOpens_eq.symm where
  hom A b hb := (X.baseIdChartIso A (sourceChart X.baseIdOpens_eq.symm b) hb).inv
  natural φ b ha hb := by
    change CoordinateMap.id.map φ.hom.toRingHom = CoordinateMap.id
    exact CoordinateMap.map_id _
  transition A b c hb hc := by
    let b' := sourceChart X.baseIdOpens_eq.symm b
    let c' := sourceChart X.baseIdOpens_eq.symm c
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change ((X.baseChangeAlong (AlgHom.id O R)).transition A
      (sourceChart X.baseIdOpens_eq b') (sourceChart X.baseIdOpens_eq c') hb hc).hom.toHom.toCoordinateMap.comp
        CoordinateMap.id =
      CoordinateMap.id.comp (X.transition A b' c' hb hc).hom.toHom.toCoordinateMap
    rw [CoordinateMap.comp_id, CoordinateMap.id_comp, X.baseIdTransition_coordinates]

/-- Extension along the identity is isomorphic to the original actual formal atlas. -/
def baseIdIso : Iso (X.baseChangeAlong (AlgHom.id O R)) X X.baseIdOpens_eq where
  hom := X.baseIdHom
  inv := X.baseIdInv
  inv_hom := by
    apply Hom.ext
    intro A b hb
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change CoordinateMap.id.comp CoordinateMap.id = CoordinateMap.id
    exact CoordinateMap.id_comp _
  hom_inv := by
    apply Hom.ext
    intro A b hb
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change CoordinateMap.id.comp CoordinateMap.id = CoordinateMap.id
    exact CoordinateMap.id_comp _

/-- The identity-extension family comparison evaluates at its selected original chart. -/
theorem baseIdPointEquiv_component (A : CommAlgCat.{v} R)
    (x : X.Point (restrictCoefficientAlgebra (AlgHom.id O R) A))
    (B : CommAlgCat.{v} R) (φ : A ⟶ B) (b : X.opens)
    (hb : IsUnit (algebraMap R B b.val)) :
    (X.baseChangeAlongPointEquiv (AlgHom.id O R) A x).val
      ⟨B, φ, sourceChart X.baseIdOpens_eq b, hb⟩ =
        x.val ⟨restrictCoefficientAlgebra (AlgHom.id O R) B,
          restrictCoefficientMap (AlgHom.id O R) φ, X.baseIdSource b,
          X.baseSource_unit (coefficientTest (AlgHom.id O R)) B _ hb⟩ := by
  let b' := sourceChart X.baseIdOpens_eq b
  exact (X.baseChange (coefficientTest (AlgHom.id O R))).reAlgebraPointEquiv_apply _
    (coefficientAlgebraAlong_eq (AlgHom.id O R)) A
    (X.toBaseChangePoints (coefficientTest (AlgHom.id O R)) A x) B φ b' hb

/-- The forward formal comparison realizes identity restriction on complete families. -/
theorem baseId_onPoints (A : CommAlgCat.{v} R)
    (x : X.Point (restrictCoefficientAlgebra (AlgHom.id O R) A)) :
    X.baseIdIso.onPoints A (X.baseChangeAlongPointEquiv (AlgHom.id O R) A x) =
      X.mapPoints (identityTestHom (O := O) A) x := by
  apply Subtype.ext
  funext t
  change SeriesPoint.eval CoordinateMap.id
    ((X.baseChangeAlongPointEquiv (AlgHom.id O R) A x).val
      ⟨t.algebra, t.map, sourceChart X.baseIdOpens_eq t.chart, t.isUnit⟩) =
        x.val ⟨t.algebra, identityTestHom (O := O) A ≫ t.map, t.chart, t.isUnit⟩
  refine (SeriesPoint.eval_id _).trans ?_
  refine (X.baseIdPointEquiv_component A x t.algebra t.map t.chart t.isUnit).trans ?_
  let a := X.baseIdSource t.chart
  have ha : IsUnit (algebraMap R (restrictCoefficientAlgebra (AlgHom.id O R) t.algebra) a.val) :=
    X.baseSource_unit (coefficientTest (AlgHom.id O R)) t.algebra
      (sourceChart X.baseIdOpens_eq t.chart) t.isUnit
  have ha' : IsUnit (algebraMap R t.algebra a.val) := X.baseIdSource_unit t.algebra t.chart t.isUnit
  have hn := x.property.1 (restrictCoefficientAlgebra (AlgHom.id O R) t.algebra) t.algebra
    (restrictCoefficientMap (AlgHom.id O R) t.map) (identityTestHom (O := O) t.algebra)
    a ha ha'
  have hm := pointMap_apply (X.chart a) (identityTestHom (O := O) t.algebra) ha ha'
    (x.val ⟨restrictCoefficientAlgebra (AlgHom.id O R) t.algebra,
      restrictCoefficientMap (AlgHom.id O R) t.map, a, ha⟩)
  exact (SeriesPoint.map_id _).symm.trans (hm.symm.trans
    (hn.trans (X.family_chart_eq x t.algebra (identityTestHom (O := O) A ≫ t.map)
      a t.chart ha' t.isUnit (X.baseIdSource_eq t.chart))))

/-- The formal inverse realizes the reverse complete-family square. -/
theorem baseId_inv_onPoints (A : CommAlgCat.{v} R)
    (x : X.Point (restrictCoefficientAlgebra (AlgHom.id O R) A)) :
    (X.baseIdIso.onPoints A).symm (X.mapPoints (identityTestHom (O := O) A) x) =
      X.baseChangeAlongPointEquiv (AlgHom.id O R) A x :=
  (LinearEquiv.symm_apply_eq (X.baseIdIso.onPoints A)).mpr
    (X.baseId_onPoints A x).symm

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
