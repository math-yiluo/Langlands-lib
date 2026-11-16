import Langlands.Geometry.FormalGroup.AtlasRationalBaseChangeAlongComposition
import Langlands.Geometry.FormalGroup.AtlasOrderRationalBaseChangeAlong
import Langlands.Geometry.FormalGroup.AtlasOrderBaseChangeAlongComposition

/-! # Full-order rational comparison of successive supplied coefficient maps -/

noncomputable section

universe u v w z

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

variable {O : Type u} [CommRing O]
variable {R S T : Type v} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra O R] [Algebra O S] [Algebra O T]
variable {D : Type w} [Ring D] [Algebra O D]
variable {F : Type z} [Field F] [Algebra O F]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {E : OrderAction D X} {E' : OrderAction D Y}
variable {h : X.opens = Y.opens}

namespace Hom

/-- The actual full-order supplied-map comparison is natural in integral maps. -/
theorem baseAlongComp_natural (q : Hom E E' h)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) :
    (E'.baseAlongCompIso f g).hom.comp
        (h := baseAlongCompMapOpens_eq X Y f g h)
        ((q.baseChangeAlong f).baseChangeAlong g) =
      (q.baseChangeAlong (g.comp f)).comp (E.baseAlongCompIso f g).hom := by
  apply Subtype.ext
  change (E'.baseAlongCompIso f g).hom.val.comp
      ((q.baseChangeAlong f).baseChangeAlong g).val =
    (q.baseChangeAlong (g.comp f)).val.comp (E.baseAlongCompIso f g).hom.val
  rw [baseChangeAlong_val (h := baseAlongOpens_eq X Y f h) (q.baseChangeAlong f) g,
    baseChangeAlong_val q f, baseChangeAlong_val q (g.comp f),
    baseAlongCompIso_hom_val, baseAlongCompIso_hom_val]
  exact BasicAtlas.Hom.baseAlongComp_natural q.val f g

/-- The actual inverse full-order comparison gives the reverse integral square. -/
theorem baseAlongComp_inv_natural (q : Hom E E' h)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) :
    ((q.baseChangeAlong f).baseChangeAlong g).comp
        (k := baseAlongCompMapOpens_eq X Y f g h) (E.baseAlongCompIso f g).inv =
      (E'.baseAlongCompIso f g).inv.comp (q.baseChangeAlong (g.comp f)) := by
  apply Subtype.ext
  change ((q.baseChangeAlong f).baseChangeAlong g).val.comp
      (E.baseAlongCompIso f g).inv.val =
    (E'.baseAlongCompIso f g).inv.val.comp (q.baseChangeAlong (g.comp f)).val
  rw [baseChangeAlong_val (h := baseAlongOpens_eq X Y f h) (q.baseChangeAlong f) g,
    baseChangeAlong_val q f, baseChangeAlong_val q (g.comp f),
    baseAlongCompIso_inv_val, baseAlongCompIso_inv_val]
  exact BasicAtlas.Hom.baseAlongComp_inv_natural q.val f g

end Hom

namespace RationalHom

/-- Supplied-map comparison is natural on the entire full-order rational centralizer. -/
theorem baseAlongComp_natural (q : RationalHom F E E' h)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) :
    comp (h := baseAlongCompMapOpens_eq X Y f g h)
      (ofHom (F := F) (E'.baseAlongCompIso f g).hom)
      (baseChangeAlong (E := E.baseChangeAlong f) (E' := E'.baseChangeAlong f)
        (h := baseAlongOpens_eq X Y f h) g
        (baseChangeAlong (E := E) (E' := E') (h := h) f q)) =
      comp (baseChangeAlong (E := E) (E' := E') (h := h) (g.comp f) q)
        (ofHom (E.baseAlongCompIso f g).hom) := by
  apply ext
  simp only [comp_val, ofHom_val, baseAlongCompIso_hom_val, baseChangeAlong_val]
  exact BasicAtlas.RationalHom.baseAlongComp_natural q.val f g

/-- The inverse comparison is natural in every full-order rational map. -/
theorem baseAlongComp_inv_natural (q : RationalHom F E E' h)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) :
    comp (k := baseAlongCompMapOpens_eq X Y f g h)
      (baseChangeAlong (E := E.baseChangeAlong f) (E' := E'.baseChangeAlong f)
        (h := baseAlongOpens_eq X Y f h) g
        (baseChangeAlong (E := E) (E' := E') (h := h) f q))
      (ofHom (F := F) (E.baseAlongCompIso f g).inv) =
      comp (ofHom (E'.baseAlongCompIso f g).inv)
        (baseChangeAlong (E := E) (E' := E') (h := h) (g.comp f) q) := by
  apply ext
  simp only [comp_val, ofHom_val, baseAlongCompIso_inv_val, baseChangeAlong_val]
  exact BasicAtlas.RationalHom.baseAlongComp_inv_natural q.val f g

end RationalHom

section FractionField

variable [IsDomain O] [IsFractionRing O F]

/-- Rationalize the actual full-order comparison for two supplied coefficient maps. -/
def baseAlongCompQuasiIsogeny (E : OrderAction D X)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) :
    QuasiIsogeny F ((E.baseChangeAlong f).baseChangeAlong g)
      (E.baseChangeAlong (g.comp f)) (X.baseAlongCompOpens_eq f g) :=
  QuasiIsogeny.ofIso (E.baseAlongCompIso f g)

@[simp]
theorem baseAlongCompQuasiIsogeny_hom (E : OrderAction D X)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) :
    (E.baseAlongCompQuasiIsogeny (F := F) f g).hom =
      RationalHom.ofHom (E.baseAlongCompIso f g).hom := rfl

@[simp]
theorem baseAlongCompQuasiIsogeny_inv (E : OrderAction D X)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) :
    (E.baseAlongCompQuasiIsogeny (F := F) f g).inv =
      RationalHom.ofHom (E.baseAlongCompIso f g).inv := rfl

/-- Forgetting the order recovers the entire actual ambient supplied-map comparison. -/
@[simp]
theorem baseAlongCompQuasiIsogeny_toAtlas (E : OrderAction D X)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) :
    (E.baseAlongCompQuasiIsogeny (F := F) f g).toAtlasQuasiIsogeny =
      X.baseAlongCompQuasiIsogeny f g := by
  apply BasicAtlas.QuasiIsogeny.ext_hom
  change BasicAtlas.RationalHom.ofHom (E.baseAlongCompIso f g).hom.val =
    BasicAtlas.RationalHom.ofHom (X.baseAlongCompIso f g).hom
  rw [baseAlongCompIso_hom_val]

namespace QuasiIsogeny

/-- Successive supplied extension commutes with the actual full-order comparison. -/
theorem baseAlongComp_natural (q : QuasiIsogeny F E E' h)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) :
    ((q.baseChangeAlong f).baseChangeAlong g).trans
        (h := baseAlongCompMapOpens_eq X Y f g h) (E'.baseAlongCompQuasiIsogeny f g) =
      (E.baseAlongCompQuasiIsogeny f g).trans (q.baseChangeAlong (g.comp f)) := by
  apply ext_hom
  exact RationalHom.baseAlongComp_natural q.hom f g

/-- The actual inverse comparison gives the reverse full-order quasi-isogeny square. -/
theorem baseAlongComp_inv_natural (q : QuasiIsogeny F E E' h)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) :
    (E.baseAlongCompQuasiIsogeny f g).symm.trans
        (k := baseAlongCompMapOpens_eq X Y f g h)
        ((q.baseChangeAlong f).baseChangeAlong g) =
      (q.baseChangeAlong (g.comp f)).trans (E'.baseAlongCompQuasiIsogeny f g).symm := by
  apply ext_hom
  exact RationalHom.baseAlongComp_inv_natural q.hom f g

end QuasiIsogeny

end FractionField

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction
