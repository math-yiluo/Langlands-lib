import Langlands.Geometry.FormalGroup.AtlasRationalBaseChangeSelf
import Langlands.Geometry.FormalGroup.AtlasOrderRationalBaseChangeAlong
import Langlands.Geometry.FormalGroup.AtlasOrderBaseChangeSelf

/-! # Full-order naturality of the actual identity coefficient comparison -/

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

/-- The actual full-order identity comparison is natural in integral full-order maps. -/
theorem baseId_natural (f : Hom E E' h) :
    E'.baseIdHom.comp (h := baseAlongOpens_eq X Y (AlgHom.id O R) h)
        (f.baseChangeAlong (AlgHom.id O R)) =
      f.comp E.baseIdHom := by
  apply Subtype.ext
  change E'.baseIdHom.val.comp (f.baseChangeAlong (AlgHom.id O R)).val =
    f.val.comp E.baseIdHom.val
  rw [baseIdHom_val, baseIdHom_val, baseChangeAlong_val]
  exact BasicAtlas.Hom.baseId_natural f.val

/-- The reverse identity comparison is natural in integral full-order maps. -/
theorem baseId_inv_natural (f : Hom E E' h) :
    (f.baseChangeAlong (AlgHom.id O R)).comp
        (k := baseAlongOpens_eq X Y (AlgHom.id O R) h) E.baseIdInv =
      E'.baseIdInv.comp f := by
  apply Subtype.ext
  change (f.baseChangeAlong (AlgHom.id O R)).val.comp E.baseIdInv.val =
    E'.baseIdInv.val.comp f.val
  rw [baseIdInv_val, baseIdInv_val, baseChangeAlong_val]
  exact BasicAtlas.Hom.baseId_inv_natural f.val

end Hom

namespace RationalHom

/-- The identity comparison is natural in every chartwise full-order rational centralizer. -/
theorem baseId_natural (f : RationalHom F E E' h) :
    comp (h := baseAlongOpens_eq X Y (AlgHom.id O R) h)
      (ofHom (F := F) E'.baseIdHom)
      (baseChangeAlong (E := E) (E' := E') (h := h) (AlgHom.id O R) f) =
      comp f (ofHom E.baseIdHom) := by
  apply ext
  simp only [comp_val, ofHom_val, baseIdHom_val, baseChangeAlong_val]
  exact BasicAtlas.RationalHom.baseId_natural f.val

/-- The reverse comparison is natural in the same full-order rational map. -/
theorem baseId_inv_natural (f : RationalHom F E E' h) :
    comp (k := baseAlongOpens_eq X Y (AlgHom.id O R) h)
      (baseChangeAlong (E := E) (E' := E') (h := h) (AlgHom.id O R) f)
      (ofHom (F := F) E.baseIdInv) =
      comp (ofHom E'.baseIdInv) f := by
  apply ext
  simp only [comp_val, ofHom_val, baseIdInv_val, baseChangeAlong_val]
  exact BasicAtlas.RationalHom.baseId_inv_natural f.val

end RationalHom

section FractionField

variable [IsDomain O] [IsFractionRing O F]

/-- Rationalize both actual maps of the full-order identity coefficient comparison. -/
def baseIdQuasiIsogeny (E : OrderAction D X) :
    QuasiIsogeny F (E.baseChangeAlong (AlgHom.id O R)) E X.baseIdOpens_eq :=
  QuasiIsogeny.ofIso E.baseIdIso

@[simp]
theorem baseIdQuasiIsogeny_hom (E : OrderAction D X) :
    (E.baseIdQuasiIsogeny (F := F)).hom = RationalHom.ofHom E.baseIdHom := rfl

@[simp]
theorem baseIdQuasiIsogeny_inv (E : OrderAction D X) :
    (E.baseIdQuasiIsogeny (F := F)).inv = RationalHom.ofHom E.baseIdInv := rfl

/-- Forgetting order commutation gives exactly the actual ambient rational comparison. -/
@[simp]
theorem baseIdQuasiIsogeny_toAtlas (E : OrderAction D X) :
    (E.baseIdQuasiIsogeny (F := F)).toAtlasQuasiIsogeny =
      X.baseIdQuasiIsogeny := by
  apply BasicAtlas.QuasiIsogeny.ext_hom
  rfl

namespace QuasiIsogeny

/-- Identity extension commutes with the full-order rational comparison. -/
theorem baseId_natural (f : QuasiIsogeny F E E' h) :
    (f.baseChangeAlong (AlgHom.id O R)).trans
        (h := baseAlongOpens_eq X Y (AlgHom.id O R) h) E'.baseIdQuasiIsogeny =
      E.baseIdQuasiIsogeny.trans f := by
  apply ext_hom
  exact RationalHom.baseId_natural f.hom

/-- The reverse full-order comparison gives the reverse quasi-isogeny square. -/
theorem baseId_inv_natural (f : QuasiIsogeny F E E' h) :
    E.baseIdQuasiIsogeny.symm.trans
        (k := baseAlongOpens_eq X Y (AlgHom.id O R) h)
        (f.baseChangeAlong (AlgHom.id O R)) =
      f.trans E'.baseIdQuasiIsogeny.symm := by
  apply ext_hom
  exact RationalHom.baseId_inv_natural f.hom

end QuasiIsogeny

end FractionField

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction
