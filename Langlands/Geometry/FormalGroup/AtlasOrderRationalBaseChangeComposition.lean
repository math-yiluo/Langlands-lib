import Langlands.Geometry.FormalGroup.AtlasRationalBaseChangeComposition
import Langlands.Geometry.FormalGroup.AtlasOrderRationalBaseChange
import Langlands.Geometry.FormalGroup.AtlasOrderBaseChangeComposition

/-! # Full-order naturality of successive rational coefficient comparisons -/

noncomputable section

universe u v w z

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {F : Type z} [Field F] [Algebra O F]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {E : OrderAction D X} {E' : OrderAction D Y}
variable {h : X.opens = Y.opens}

attribute [local instance] coefficientAlgebra coefficientScalarTower

namespace Hom

/-- The actual full-order successive-extension comparison is natural in integral maps. -/
theorem baseComp_natural (f : Hom E E' h) (S : CommAlgCat.{v} R)
    (T : CommAlgCat.{v} S) :
    (E'.baseCompHom S T).comp
        (h := baseOpens_eq T (baseOpens_eq S h)) ((f.baseChange S).baseChange T) =
      (f.baseChange (restrictTest S T)).comp (E.baseCompHom S T) := by
  apply Subtype.ext
  change (E'.baseCompHom S T).val.comp ((f.baseChange S).baseChange T).val =
    (f.baseChange (restrictTest S T)).val.comp (E.baseCompHom S T).val
  rw [baseCompHom_val, baseCompHom_val, baseChange_val, baseChange_val, baseChange_val]
  exact BasicAtlas.Hom.baseComp_natural f.val S T

/-- The actual reverse full-order comparison gives the reverse integral square. -/
theorem baseComp_inv_natural (f : Hom E E' h) (S : CommAlgCat.{v} R)
    (T : CommAlgCat.{v} S) :
    ((f.baseChange S).baseChange T).comp
        (k := baseOpens_eq T (baseOpens_eq S h)) (E.baseCompInv S T) =
      (E'.baseCompInv S T).comp (f.baseChange (restrictTest S T)) := by
  apply Subtype.ext
  change ((f.baseChange S).baseChange T).val.comp (E.baseCompInv S T).val =
    (E'.baseCompInv S T).val.comp (f.baseChange (restrictTest S T)).val
  rw [baseCompInv_val, baseCompInv_val, baseChange_val, baseChange_val, baseChange_val]
  exact BasicAtlas.Hom.baseComp_inv_natural f.val S T

end Hom

namespace RationalHom

/-- The successive comparison is natural in every full-order rational centralizer. -/
theorem baseComp_natural (f : RationalHom F E E' h) (S : CommAlgCat.{v} R)
    (T : CommAlgCat.{v} S) :
    comp (h := baseOpens_eq T (baseOpens_eq S h))
      (ofHom (F := F) (E'.baseCompHom S T))
      (baseChange (E := E.baseChange S) (E' := E'.baseChange S)
        (h := baseOpens_eq S h) T (baseChange (E := E) (E' := E') (h := h) S f)) =
      comp (baseChange (E := E) (E' := E') (h := h) (restrictTest S T) f)
        (ofHom (E.baseCompHom S T)) := by
  apply ext
  simp only [comp_val, ofHom_val, baseCompHom_val, baseChange_val]
  exact BasicAtlas.RationalHom.baseComp_natural f.val S T

/-- The reverse comparison is natural in the same entire rational centralizer. -/
theorem baseComp_inv_natural (f : RationalHom F E E' h) (S : CommAlgCat.{v} R)
    (T : CommAlgCat.{v} S) :
    comp (k := baseOpens_eq T (baseOpens_eq S h))
      (baseChange (E := E.baseChange S) (E' := E'.baseChange S)
        (h := baseOpens_eq S h) T (baseChange (E := E) (E' := E') (h := h) S f))
      (ofHom (F := F) (E.baseCompInv S T)) =
      comp (ofHom (E'.baseCompInv S T))
        (baseChange (E := E) (E' := E') (h := h) (restrictTest S T) f) := by
  apply ext
  simp only [comp_val, ofHom_val, baseCompInv_val, baseChange_val]
  exact BasicAtlas.RationalHom.baseComp_inv_natural f.val S T

end RationalHom

section FractionField

variable [IsDomain O] [IsFractionRing O F]

/-- Rationalize both actual maps of the full-order successive-extension comparison. -/
def baseCompQuasiIsogeny (E : OrderAction D X)
    (S : CommAlgCat.{v} R) (T : CommAlgCat.{v} S) :
    QuasiIsogeny F ((E.baseChange S).baseChange T)
      (E.baseChange (restrictTest S T)) (X.baseCompOpens_eq S T) :=
  QuasiIsogeny.ofIso (E.baseCompIso S T)

@[simp]
theorem baseCompQuasiIsogeny_hom (E : OrderAction D X)
    (S : CommAlgCat.{v} R) (T : CommAlgCat.{v} S) :
    (E.baseCompQuasiIsogeny (F := F) S T).hom =
      RationalHom.ofHom (E.baseCompHom S T) := rfl

@[simp]
theorem baseCompQuasiIsogeny_inv (E : OrderAction D X)
    (S : CommAlgCat.{v} R) (T : CommAlgCat.{v} S) :
    (E.baseCompQuasiIsogeny (F := F) S T).inv =
      RationalHom.ofHom (E.baseCompInv S T) := rfl

/-- Forgetting the order recovers the entire actual ambient comparison. -/
@[simp]
theorem baseCompQuasiIsogeny_toAtlas (E : OrderAction D X)
    (S : CommAlgCat.{v} R) (T : CommAlgCat.{v} S) :
    (E.baseCompQuasiIsogeny (F := F) S T).toAtlasQuasiIsogeny =
      X.baseCompQuasiIsogeny S T := by
  apply BasicAtlas.QuasiIsogeny.ext_hom
  rfl

namespace QuasiIsogeny

/-- The actual successive-extension comparison is natural in full-order quasi-isogenies. -/
theorem baseComp_natural (f : QuasiIsogeny F E E' h)
    (S : CommAlgCat.{v} R) (T : CommAlgCat.{v} S) :
    ((f.baseChange S).baseChange T).trans
        (h := baseOpens_eq T (baseOpens_eq S h)) (E'.baseCompQuasiIsogeny S T) =
      (E.baseCompQuasiIsogeny S T).trans (f.baseChange (restrictTest S T)) := by
  apply ext_hom
  exact RationalHom.baseComp_natural f.hom S T

/-- The reverse full-order comparison gives the reverse quasi-isogeny square. -/
theorem baseComp_inv_natural (f : QuasiIsogeny F E E' h)
    (S : CommAlgCat.{v} R) (T : CommAlgCat.{v} S) :
    (E.baseCompQuasiIsogeny S T).symm.trans
        (k := baseOpens_eq T (baseOpens_eq S h)) ((f.baseChange S).baseChange T) =
      (f.baseChange (restrictTest S T)).trans (E'.baseCompQuasiIsogeny S T).symm := by
  apply ext_hom
  exact RationalHom.baseComp_inv_natural f.hom S T

end QuasiIsogeny

end FractionField

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction
