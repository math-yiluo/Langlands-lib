import Langlands.Geometry.FormalGroup.AtlasBaseChangeMorphism

/-! # Successive coefficient extensions of actual formal atlases -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ : Type} [Finite σ]

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable (X : BasicAtlas O R σ) (S : CommAlgCat.{v} R) (T : CommAlgCat.{v} S)

/-- The successive and direct image covers have the same actual generators. -/
theorem baseCompOpens_eq :
    ((X.baseChange S).baseChange T).opens =
      (X.baseChange (restrictTest S T)).opens := by
  change algebraMap S T '' (algebraMap R S '' X.opens) =
    algebraMap R (restrictTest S T) '' X.opens
  rw [Set.image_image]
  rfl

/-- The original chart selected by successive coefficient extension. -/
abbrev baseCompIterSource (b : X.baseOpens (restrictTest S T)) : X.opens :=
  X.baseSource S ((X.baseChange S).baseSource T
    (sourceChart (X.baseCompOpens_eq S T) b))

/-- Its generator is invertible on the final coefficient test. -/
theorem baseCompIter_unit (A : CommAlgCat.{v} T)
    (b : X.baseOpens (restrictTest S T))
    (hb : IsUnit (algebraMap T A b.val)) :
    IsUnit (algebraMap R (restrictTest (restrictTest S T) A)
      (X.baseCompIterSource S T b).val) :=
  X.baseSource_unit S (restrictTest T A) _
    ((X.baseChange S).baseSource_unit T A _ hb)

/-- Compare a successive chart with the original chart it selected. -/
def baseCompLeftChartIso (A : CommAlgCat.{v} T)
    (b : X.baseOpens (restrictTest S T))
    (hb : IsUnit (algebraMap T A b.val)) :
    ModuleLaw.Iso
      ((((X.baseChange S).baseChange T).chart
        (sourceChart (X.baseCompOpens_eq S T) b)).map
          (coefficientLift (O := O) b.val A hb))
      ((X.chart (X.baseCompIterSource S T b)).map
        (coefficientLift (O := O) (X.baseCompIterSource S T b).val
          (restrictTest (restrictTest S T) A) (X.baseCompIter_unit S T A b hb))) :=
  ((X.baseChange S).baseChartIso T A (sourceChart (X.baseCompOpens_eq S T) b) hb).trans
    (X.baseChartIso S (restrictTest T A)
      ((X.baseChange S).baseSource T (sourceChart (X.baseCompOpens_eq S T) b))
        ((X.baseChange S).baseSource_unit T A _ hb))

/-- The comparison uses the actual original transition between the two choices. -/
def baseCompChartIso (A : CommAlgCat.{v} T)
    (b : X.baseOpens (restrictTest S T))
    (hb : IsUnit (algebraMap T A b.val)) :
    ModuleLaw.Iso
      ((((X.baseChange S).baseChange T).chart
        (sourceChart (X.baseCompOpens_eq S T) b)).map
          (coefficientLift (O := O) b.val A hb))
      (((X.baseChange (restrictTest S T)).chart b).map
        (coefficientLift (O := O) b.val A hb)) :=
  (X.baseCompLeftChartIso S T A b hb).trans
    ((X.transition (restrictTest (restrictTest S T) A)
      (X.baseCompIterSource S T b) (X.baseSource (restrictTest S T) b)
      (X.baseCompIter_unit S T A b hb) (X.baseSource_unit (restrictTest S T) A b hb)).trans
        (X.baseChartIso (restrictTest S T) A b hb).symm)

/-- The full formal series of the forward comparison is the original transition. -/
theorem baseCompChartIso_coordinates (A : CommAlgCat.{v} T)
    (b : X.baseOpens (restrictTest S T))
    (hb : IsUnit (algebraMap T A b.val)) :
    (X.baseCompChartIso S T A b hb).hom.toHom.toCoordinateMap =
      (X.transition (restrictTest (restrictTest S T) A)
        (X.baseCompIterSource S T b) (X.baseSource (restrictTest S T) b)
        (X.baseCompIter_unit S T A b hb)
        (X.baseSource_unit (restrictTest S T) A b hb)).hom.toHom.toCoordinateMap := by
  change (CoordinateMap.id.comp
    (X.transition (restrictTest (restrictTest S T) A)
      (X.baseCompIterSource S T b) (X.baseSource (restrictTest S T) b)
      (X.baseCompIter_unit S T A b hb)
      (X.baseSource_unit (restrictTest S T) A b hb)).hom.toHom.toCoordinateMap).comp
        (CoordinateMap.id.comp CoordinateMap.id) = _
  simp only [CoordinateMap.id_comp, CoordinateMap.comp_id]

/-- Successive transitions are the original transitions at the iterated choices. -/
theorem baseCompLeftTransition_coordinates (A : CommAlgCat.{v} T)
    (b c : X.baseOpens (restrictTest S T))
    (hb : IsUnit (algebraMap T A b.val)) (hc : IsUnit (algebraMap T A c.val)) :
    (((X.baseChange S).baseChange T).transition A
      (sourceChart (X.baseCompOpens_eq S T) b)
      (sourceChart (X.baseCompOpens_eq S T) c) hb hc).hom.toHom.toCoordinateMap =
      (X.transition (restrictTest (restrictTest S T) A)
        (X.baseCompIterSource S T b) (X.baseCompIterSource S T c)
        (X.baseCompIter_unit S T A b hb) (X.baseCompIter_unit S T A c hc)).hom.toHom.toCoordinateMap :=
  ((X.baseChange S).baseTransition_coordinates T A _ _ hb hc).trans
    (X.baseTransition_coordinates S (restrictTest T A) _ _ _ _)

/-- Successive coefficient extension compares to direct extension by a formal map. -/
def baseCompHom :
    Hom ((X.baseChange S).baseChange T) (X.baseChange (restrictTest S T))
      (X.baseCompOpens_eq S T) where
  hom A b hb := (X.baseCompChartIso S T A b hb).hom
  natural φ b ha hb := by
    change ((X.baseCompChartIso S T _ b ha).hom.toHom.toCoordinateMap).map
      φ.hom.toRingHom = (X.baseCompChartIso S T _ b hb).hom.toHom.toCoordinateMap
    exact (congrArg (fun F : CoordinateMap _ σ σ => F.map φ.hom.toRingHom)
      (X.baseCompChartIso_coordinates S T _ b ha)).trans
      ((X.transition_natural (restrictTestHom (restrictTest S T) φ) _ _ _ _ _ _).trans
        (X.baseCompChartIso_coordinates S T _ b hb).symm)
  transition A b c hb hc := by
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change ((X.baseChange (restrictTest S T)).transition A b c hb hc).hom.toHom.toCoordinateMap.comp
      (X.baseCompChartIso S T A b hb).hom.toHom.toCoordinateMap =
      (X.baseCompChartIso S T A c hc).hom.toHom.toCoordinateMap.comp
        (((X.baseChange S).baseChange T).transition A
          (sourceChart (X.baseCompOpens_eq S T) b)
          (sourceChart (X.baseCompOpens_eq S T) c) hb hc).hom.toHom.toCoordinateMap
    exact (congrArg₂ (fun F G : CoordinateMap A σ σ => F.comp G)
      (X.baseTransition_coordinates (restrictTest S T) A b c hb hc)
      (X.baseCompChartIso_coordinates S T A b hb)).trans
      (((congrArg (fun f => f.hom.toHom.toCoordinateMap)
        (X.transition_cocycle (restrictTest (restrictTest S T) A)
          (X.baseCompIterSource S T b) (X.baseSource (restrictTest S T) b)
          (X.baseSource (restrictTest S T) c)
          (X.baseCompIter_unit S T A b hb) (X.baseSource_unit (restrictTest S T) A b hb)
          (X.baseSource_unit (restrictTest S T) A c hc))).trans
        (congrArg (fun f => f.hom.toHom.toCoordinateMap)
          (X.transition_cocycle (restrictTest (restrictTest S T) A)
            (X.baseCompIterSource S T b) (X.baseCompIterSource S T c)
            (X.baseSource (restrictTest S T) c)
            (X.baseCompIter_unit S T A b hb) (X.baseCompIter_unit S T A c hc)
            (X.baseSource_unit (restrictTest S T) A c hc))).symm).trans
        (congrArg₂ (fun F G : CoordinateMap A σ σ => F.comp G)
          (X.baseCompChartIso_coordinates S T A c hc)
          (X.baseCompLeftTransition_coordinates S T A b c hb hc)).symm)

/-- Reverse the comparison through the original transition in the opposite direction. -/
def baseCompInvChartIso (A : CommAlgCat.{v} T)
    (b : X.baseOpens (restrictTest S T))
    (hb : IsUnit (algebraMap T A b.val)) :
    ModuleLaw.Iso
      (((X.baseChange (restrictTest S T)).chart b).map
        (coefficientLift (O := O) b.val A hb))
      ((((X.baseChange S).baseChange T).chart
        (sourceChart (X.baseCompOpens_eq S T) b)).map
          (coefficientLift (O := O) b.val A hb)) :=
  (X.baseChartIso (restrictTest S T) A b hb).trans
    ((X.transition (restrictTest (restrictTest S T) A)
      (X.baseSource (restrictTest S T) b) (X.baseCompIterSource S T b)
      (X.baseSource_unit (restrictTest S T) A b hb) (X.baseCompIter_unit S T A b hb)).trans
        (X.baseCompLeftChartIso S T A b hb).symm)

/-- The reverse comparison retains the full reverse original transition series. -/
theorem baseCompInvChartIso_coordinates (A : CommAlgCat.{v} T)
    (b : X.baseOpens (restrictTest S T))
    (hb : IsUnit (algebraMap T A b.val)) :
    (X.baseCompInvChartIso S T A b hb).hom.toHom.toCoordinateMap =
      (X.transition (restrictTest (restrictTest S T) A)
        (X.baseSource (restrictTest S T) b) (X.baseCompIterSource S T b)
        (X.baseSource_unit (restrictTest S T) A b hb)
        (X.baseCompIter_unit S T A b hb)).hom.toHom.toCoordinateMap := by
  change ((CoordinateMap.id.comp CoordinateMap.id).comp
    (X.transition (restrictTest (restrictTest S T) A)
      (X.baseSource (restrictTest S T) b) (X.baseCompIterSource S T b)
      (X.baseSource_unit (restrictTest S T) A b hb)
      (X.baseCompIter_unit S T A b hb)).hom.toHom.toCoordinateMap).comp CoordinateMap.id = _
  simp only [CoordinateMap.id_comp, CoordinateMap.comp_id]

/-- The reverse formal map is coefficient-natural and respects every overlap. -/
def baseCompInv :
    Hom (X.baseChange (restrictTest S T)) ((X.baseChange S).baseChange T)
      (X.baseCompOpens_eq S T).symm where
  hom A b hb :=
    (X.baseCompInvChartIso S T A (sourceChart (X.baseCompOpens_eq S T).symm b) hb).hom
  natural φ b ha hb := by
    let b' := sourceChart (X.baseCompOpens_eq S T).symm b
    change ((X.baseCompInvChartIso S T _ b' ha).hom.toHom.toCoordinateMap).map
      φ.hom.toRingHom = (X.baseCompInvChartIso S T _ b' hb).hom.toHom.toCoordinateMap
    exact (congrArg (fun F : CoordinateMap _ σ σ => F.map φ.hom.toRingHom)
      (X.baseCompInvChartIso_coordinates S T _ b' ha)).trans
      ((X.transition_natural (restrictTestHom (restrictTest S T) φ) _ _ _ _ _ _).trans
        (X.baseCompInvChartIso_coordinates S T _ b' hb).symm)
  transition A b c hb hc := by
    let b' := sourceChart (X.baseCompOpens_eq S T).symm b
    let c' := sourceChart (X.baseCompOpens_eq S T).symm c
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change (((X.baseChange S).baseChange T).transition A
      (sourceChart (X.baseCompOpens_eq S T) b')
      (sourceChart (X.baseCompOpens_eq S T) c') hb hc).hom.toHom.toCoordinateMap.comp
      (X.baseCompInvChartIso S T A b' hb).hom.toHom.toCoordinateMap =
      (X.baseCompInvChartIso S T A c' hc).hom.toHom.toCoordinateMap.comp
        ((X.baseChange (restrictTest S T)).transition A b' c' hb hc).hom.toHom.toCoordinateMap
    exact (congrArg₂ (fun F G : CoordinateMap A σ σ => F.comp G)
      (X.baseCompLeftTransition_coordinates S T A b' c' hb hc)
      (X.baseCompInvChartIso_coordinates S T A b' hb)).trans
      (((congrArg (fun f => f.hom.toHom.toCoordinateMap)
        (X.transition_cocycle (restrictTest (restrictTest S T) A)
          (X.baseSource (restrictTest S T) b') (X.baseCompIterSource S T b')
          (X.baseCompIterSource S T c')
          (X.baseSource_unit (restrictTest S T) A b' hb)
          (X.baseCompIter_unit S T A b' hb) (X.baseCompIter_unit S T A c' hc))).trans
        (congrArg (fun f => f.hom.toHom.toCoordinateMap)
          (X.transition_cocycle (restrictTest (restrictTest S T) A)
            (X.baseSource (restrictTest S T) b') (X.baseSource (restrictTest S T) c')
            (X.baseCompIterSource S T c')
            (X.baseSource_unit (restrictTest S T) A b' hb)
            (X.baseSource_unit (restrictTest S T) A c' hc)
            (X.baseCompIter_unit S T A c' hc))).symm).trans
        (congrArg₂ (fun F G : CoordinateMap A σ σ => F.comp G)
          (X.baseCompInvChartIso_coordinates S T A c' hc)
          (X.baseTransition_coordinates (restrictTest S T) A b' c' hb hc)).symm)

/-- Successive and direct coefficient extensions are actually formally isomorphic. -/
def baseCompIso :
    Iso ((X.baseChange S).baseChange T) (X.baseChange (restrictTest S T))
      (X.baseCompOpens_eq S T) where
  hom := X.baseCompHom S T
  inv := X.baseCompInv S T
  inv_hom := by
    apply Hom.ext
    intro A b hb
    let b' := sourceChart (X.baseCompOpens_eq S T).symm b
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change (X.baseCompInvChartIso S T A b' hb).hom.toHom.toCoordinateMap.comp
      (X.baseCompChartIso S T A b' hb).hom.toHom.toCoordinateMap = CoordinateMap.id
    exact (congrArg₂ (fun F G : CoordinateMap A σ σ => F.comp G)
      (X.baseCompInvChartIso_coordinates S T A b' hb)
      (X.baseCompChartIso_coordinates S T A b' hb)).trans
      ((congrArg (fun f => f.hom.toHom.toCoordinateMap)
        (X.transition_cocycle (restrictTest (restrictTest S T) A)
          (X.baseCompIterSource S T b') (X.baseSource (restrictTest S T) b')
          (X.baseCompIterSource S T b') (X.baseCompIter_unit S T A b' hb)
          (X.baseSource_unit (restrictTest S T) A b' hb)
          (X.baseCompIter_unit S T A b' hb))).trans
        (congrArg (fun f => f.hom.toHom.toCoordinateMap)
          (X.transition_self (restrictTest (restrictTest S T) A)
            (X.baseCompIterSource S T b') (X.baseCompIter_unit S T A b' hb))))
  hom_inv := by
    apply Hom.ext
    intro A b hb
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change (X.baseCompChartIso S T A b hb).hom.toHom.toCoordinateMap.comp
      (X.baseCompInvChartIso S T A b hb).hom.toHom.toCoordinateMap = CoordinateMap.id
    exact (congrArg₂ (fun F G : CoordinateMap A σ σ => F.comp G)
      (X.baseCompChartIso_coordinates S T A b hb)
      (X.baseCompInvChartIso_coordinates S T A b hb)).trans
      ((congrArg (fun f => f.hom.toHom.toCoordinateMap)
        (X.transition_cocycle (restrictTest (restrictTest S T) A)
          (X.baseSource (restrictTest S T) b) (X.baseCompIterSource S T b)
          (X.baseSource (restrictTest S T) b) (X.baseSource_unit (restrictTest S T) A b hb)
          (X.baseCompIter_unit S T A b hb) (X.baseSource_unit (restrictTest S T) A b hb))).trans
        (congrArg (fun f => f.hom.toHom.toCoordinateMap)
          (X.transition_self (restrictTest (restrictTest S T) A)
            (X.baseSource (restrictTest S T) b) (X.baseSource_unit (restrictTest S T) A b hb))))

/-- The formal comparison identifies successive restriction of every complete family. -/
theorem baseComp_onPoints (A : CommAlgCat.{v} T)
    (x : X.Point (restrictTest (restrictTest S T) A)) :
    (X.baseCompIso S T).onPoints A
      ((X.baseChange S).toBaseChangePoints T A
        (X.toBaseChangePoints S (restrictTest T A) x)) =
      X.toBaseChangePoints (restrictTest S T) A x := by
  apply Subtype.ext
  funext t
  let z : SeriesPoint t.algebra σ Empty :=
    x.val ⟨restrictTest (restrictTest S T) t.algebra,
      restrictTestHom (restrictTest S T) t.map,
      X.baseCompIterSource S T t.chart, X.baseCompIter_unit S T t.algebra t.chart t.isUnit⟩
  change SeriesPoint.eval (X.baseCompChartIso S T t.algebra t.chart t.isUnit).hom.toHom.toCoordinateMap z =
    x.val ⟨restrictTest (restrictTest S T) t.algebra,
      restrictTestHom (restrictTest S T) t.map,
      X.baseSource (restrictTest S T) t.chart,
      X.baseSource_unit (restrictTest S T) t.algebra t.chart t.isUnit⟩
  exact (congrArg (fun F : CoordinateMap t.algebra σ σ => SeriesPoint.eval F z)
    (X.baseCompChartIso_coordinates S T t.algebra t.chart t.isUnit)).trans
      (x.property.2 (restrictTest (restrictTest S T) t.algebra)
        (restrictTestHom (restrictTest S T) t.map)
        (X.baseCompIterSource S T t.chart) (X.baseSource (restrictTest S T) t.chart)
        (X.baseCompIter_unit S T t.algebra t.chart t.isUnit)
        (X.baseSource_unit (restrictTest S T) t.algebra t.chart t.isUnit))

/-- Its formal inverse realizes the reverse complete-family square. -/
theorem baseComp_inv_onPoints (A : CommAlgCat.{v} T)
    (x : X.Point (restrictTest (restrictTest S T) A)) :
    ((X.baseCompIso S T).onPoints A).symm
      (X.toBaseChangePoints (restrictTest S T) A x) =
      (X.baseChange S).toBaseChangePoints T A
        (X.toBaseChangePoints S (restrictTest T A) x) :=
  (LinearEquiv.symm_apply_eq ((X.baseCompIso S T).onPoints A)).mpr
    (X.baseComp_onPoints S T A x).symm

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
