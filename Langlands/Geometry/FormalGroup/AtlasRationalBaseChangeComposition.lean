import Langlands.Geometry.FormalGroup.AtlasRationalBaseChange
import Langlands.Geometry.FormalGroup.AtlasBaseChangeComposition

/-! # Natural rational comparison of successive coefficient extensions -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory TensorProduct

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {F : Type w} [Field F] [Algebra O F]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {h : X.opens = Y.opens}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Iterated preimage choices respect equality of the original covers. -/
theorem baseCompIterSource_sourceChart (S : CommAlgCat.{v} R) (T : CommAlgCat.{v} S)
    (h : X.opens = Y.opens) (b : Y.baseOpens (restrictTest S T)) :
    X.baseCompIterSource S T (sourceChart (baseOpens_eq (restrictTest S T) h) b) =
      sourceChart h (Y.baseCompIterSource S T b) := by
  change X.baseSource S ((X.baseChange S).baseSource T _) = _
  have he :
      sourceChart (X.baseCompOpens_eq S T)
          (sourceChart (baseOpens_eq (restrictTest S T) h) b) =
        sourceChart (baseOpens_eq T (baseOpens_eq S h))
          (sourceChart (Y.baseCompOpens_eq S T) b) := rfl
  exact (congrArg (fun c : ((X.baseChange S).baseChange T).opens =>
    X.baseSource S ((X.baseChange S).baseSource T c)) he).trans
      ((congrArg (fun c : (X.baseChange S).opens => X.baseSource S c)
        (baseSource_sourceChart (X := X.baseChange S) (Y := Y.baseChange S)
          T (baseOpens_eq S h)
          (show (Y.baseChange S).baseOpens T from
            sourceChart (X := (Y.baseChange S).baseChange T)
              (Y := Y.baseChange (restrictTest S T)) (Y.baseCompOpens_eq S T) b))).trans
        (baseSource_sourceChart S h _))

namespace Hom

/-- The actual successive-extension comparison is natural in integral formal maps. -/
theorem baseComp_natural (f : Hom X Y h) (S : CommAlgCat.{v} R)
    (T : CommAlgCat.{v} S) :
    (Y.baseCompHom S T).comp
        (h := baseOpens_eq T (baseOpens_eq S h)) ((f.baseChange S).baseChange T) =
      (f.baseChange (restrictTest S T)).comp (X.baseCompHom S T) := by
  apply Hom.ext
  intro A b hb
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  change (Y.baseCompChartIso S T A b hb).hom.toHom.toCoordinateMap.comp
      (((f.baseChange S).baseChange T).hom A
        (sourceChart (Y.baseCompOpens_eq S T) b) hb).toHom.toCoordinateMap =
    ((f.baseChange (restrictTest S T)).hom A b hb).toHom.toCoordinateMap.comp
      (X.baseCompChartIso S T A
        (sourceChart (baseOpens_eq (restrictTest S T) h) b) hb).hom.toHom.toCoordinateMap
  refine (congrArg₂
    (fun (q : CoordinateMap A τ τ) (z : CoordinateMap A σ τ) => q.comp z)
    (Y.baseCompChartIso_coordinates S T A b hb)
    (((f.baseChange S).baseChange_coordinates T A _ hb).trans
      (f.baseChange_coordinates S (restrictTest T A) _ _))).trans ?_
  refine (congrArg (fun q => q.toHom.toCoordinateMap)
    (f.transition (restrictTest (restrictTest S T) A)
      (Y.baseCompIterSource S T b) (Y.baseSource (restrictTest S T) b)
      (Y.baseCompIter_unit S T A b hb)
      (Y.baseSource_unit (restrictTest S T) A b hb))).trans ?_
  exact (congrArg₂
    (fun (q : CoordinateMap A σ τ) (z : CoordinateMap A σ σ) => q.comp z)
    (f.baseChange_coordinates (restrictTest S T) A b hb)
    ((X.baseCompChartIso_coordinates S T A
      (sourceChart (baseOpens_eq (restrictTest S T) h) b) hb).trans
      (X.testTransition_coordinates_eq (restrictTest (restrictTest S T) A)
        _ _ _ _ _ _ _ _ (baseCompIterSource_sourceChart S T h b)
          (baseSource_sourceChart (restrictTest S T) h b)))).symm

/-- Its actual inverse gives the reverse successive-extension square. -/
theorem baseComp_inv_natural (f : Hom X Y h) (S : CommAlgCat.{v} R)
    (T : CommAlgCat.{v} S) :
    ((f.baseChange S).baseChange T).comp
        (k := baseOpens_eq T (baseOpens_eq S h)) (X.baseCompInv S T) =
      (Y.baseCompInv S T).comp (f.baseChange (restrictTest S T)) := by
  calc
    ((f.baseChange S).baseChange T).comp
        (k := baseOpens_eq T (baseOpens_eq S h)) (X.baseCompInv S T) =
        ((Y.baseCompIso S T).inv.comp (Y.baseCompIso S T).hom).comp
          (((f.baseChange S).baseChange T).comp
            (k := baseOpens_eq T (baseOpens_eq S h)) (X.baseCompInv S T)) := by
      rw [(Y.baseCompIso S T).inv_hom, id_comp]
    _ = (Y.baseCompIso S T).inv.comp
        (((Y.baseCompHom S T).comp
          (h := baseOpens_eq T (baseOpens_eq S h)) ((f.baseChange S).baseChange T)).comp
            (X.baseCompInv S T)) := by
      exact (comp_assoc _ _ _).trans
        (congrArg (fun z => (Y.baseCompIso S T).inv.comp z)
          (comp_assoc (Y.baseCompHom S T) ((f.baseChange S).baseChange T)
            (X.baseCompInv S T)).symm)
    _ = (Y.baseCompInv S T).comp (f.baseChange (restrictTest S T)) := by
      rw [f.baseComp_natural, comp_assoc]
      exact (congrArg
        (fun z => (Y.baseCompInv S T).comp ((f.baseChange (restrictTest S T)).comp z))
        (X.baseCompIso S T).hom_inv).trans
          (congrArg (fun z => (Y.baseCompInv S T).comp z)
            (comp_id (f.baseChange (restrictTest S T))))

end Hom

namespace RationalHom

/-- Global rational maps commute with the actual successive-extension comparison. -/
theorem baseComp_natural (f : RationalHom F X Y h) (S : CommAlgCat.{v} R)
    (T : CommAlgCat.{v} S) :
    comp (h := baseOpens_eq T (baseOpens_eq S h))
      (ofHom (F := F) (Y.baseCompHom S T))
      (baseChange (X := X.baseChange S) (Y := Y.baseChange S) (h := baseOpens_eq S h) T
        (baseChange (X := X) (Y := Y) (h := h) S f)) =
      comp (baseChange (X := X) (Y := Y) (h := h) (restrictTest S T) f)
        (ofHom (X.baseCompHom S T)) := by
  induction f using TensorProduct.inductionOn with
  | add f g hf hg =>
    simp only [_root_.map_add, comp_add, add_comp, hf, hg]
  | tmul a f =>
    simp only [ofHom_apply, baseChange_tmul, comp_tmul, one_mul, mul_one,
      Hom.baseComp_natural]

/-- The actual reverse comparison gives the reverse global rational square. -/
theorem baseComp_inv_natural (f : RationalHom F X Y h) (S : CommAlgCat.{v} R)
    (T : CommAlgCat.{v} S) :
    comp (k := baseOpens_eq T (baseOpens_eq S h))
      (baseChange (X := X.baseChange S) (Y := Y.baseChange S) (h := baseOpens_eq S h) T
        (baseChange (X := X) (Y := Y) (h := h) S f))
      (ofHom (F := F) (X.baseCompInv S T)) =
      comp (ofHom (Y.baseCompInv S T))
        (baseChange (X := X) (Y := Y) (h := h) (restrictTest S T) f) := by
  induction f using TensorProduct.inductionOn with
  | add f g hf hg =>
    simp only [_root_.map_add, comp_add, add_comp, hf, hg]
  | tmul a f =>
    simp only [ofHom_apply, baseChange_tmul, comp_tmul, one_mul, mul_one,
      Hom.baseComp_inv_natural]

end RationalHom

section FractionField

variable [IsDomain O] [IsFractionRing O F]

/-- Rationalize both actual maps comparing successive and direct coefficient extension. -/
def baseCompQuasiIsogeny (X : BasicAtlas O R σ)
    (S : CommAlgCat.{v} R) (T : CommAlgCat.{v} S) :
    QuasiIsogeny F ((X.baseChange S).baseChange T)
      (X.baseChange (restrictTest S T)) (X.baseCompOpens_eq S T) :=
  QuasiIsogeny.ofIso (X.baseCompIso S T)

@[simp]
theorem baseCompQuasiIsogeny_hom (X : BasicAtlas O R σ)
    (S : CommAlgCat.{v} R) (T : CommAlgCat.{v} S) :
    (X.baseCompQuasiIsogeny (F := F) S T).hom =
      RationalHom.ofHom (X.baseCompHom S T) := rfl

@[simp]
theorem baseCompQuasiIsogeny_inv (X : BasicAtlas O R σ)
    (S : CommAlgCat.{v} R) (T : CommAlgCat.{v} S) :
    (X.baseCompQuasiIsogeny (F := F) S T).inv =
      RationalHom.ofHom (X.baseCompInv S T) := rfl

namespace QuasiIsogeny

/-- The chosen successive-extension comparison is natural in actual quasi-isogenies. -/
theorem baseComp_natural (f : QuasiIsogeny F X Y h)
    (S : CommAlgCat.{v} R) (T : CommAlgCat.{v} S) :
    ((f.baseChange S).baseChange T).trans
        (h := baseOpens_eq T (baseOpens_eq S h)) (Y.baseCompQuasiIsogeny S T) =
      (X.baseCompQuasiIsogeny S T).trans (f.baseChange (restrictTest S T)) := by
  apply ext_hom
  exact RationalHom.baseComp_natural f.hom S T

/-- The reverse chosen comparison gives the reverse quasi-isogeny square. -/
theorem baseComp_inv_natural (f : QuasiIsogeny F X Y h)
    (S : CommAlgCat.{v} R) (T : CommAlgCat.{v} S) :
    (X.baseCompQuasiIsogeny S T).symm.trans
        (k := baseOpens_eq T (baseOpens_eq S h)) ((f.baseChange S).baseChange T) =
      (f.baseChange (restrictTest S T)).trans (Y.baseCompQuasiIsogeny S T).symm := by
  apply ext_hom
  exact RationalHom.baseComp_inv_natural f.hom S T

end QuasiIsogeny

end FractionField

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
