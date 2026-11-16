import Langlands.Geometry.FormalGroup.AtlasRationalBaseChangeAlong
import Langlands.Geometry.FormalGroup.AtlasOrderRationalBaseChange
import Langlands.Geometry.FormalGroup.AtlasOrderBaseChangeAlong

/-! # Full-order rational atlas maps over supplied scalar structures -/

noncomputable section

universe u v w z

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R S : Type v} [CommRing R] [CommRing S]
variable {D : Type w} [Ring D] [Algebra O D]
variable {F : Type z} [Field F] [Algebra O F]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Equal scalar structures retain equal covers, with both transported atlases specified. -/
theorem reAlgebraOpens_eq {α : Algebra O R}
    (X : @BasicAtlas O _ R _ α σ _) (Y : @BasicAtlas O _ R _ α τ _)
    (β : Algebra O R) (e : α = β) (h : (letI := α; X.opens = Y.opens)) :
    (letI := β; (X.reAlgebra β e).opens = (Y.reAlgebra β e).opens) := h

/-- Supplied-target atlases retain equality of the original principal covers. -/
theorem baseAlongOpens_eq [Algebra O R] [Algebra O S]
    (X : BasicAtlas O R σ) (Y : BasicAtlas O R τ) (f : R →ₐ[O] S)
    (h : X.opens = Y.opens) :
    (X.baseChangeAlong f).opens = (Y.baseChangeAlong f).opens :=
  baseOpens_eq (coefficientTest f) h

namespace OrderAction

namespace RationalHom

section AlgebraTransport

variable {α : Algebra O R}
variable {X : @BasicAtlas O _ R _ α σ _}
variable {Y : @BasicAtlas O _ R _ α τ _}
variable {Z : @BasicAtlas O _ R _ α υ _}
variable {E : (letI := α; OrderAction D X)}
variable {E' : (letI := α; OrderAction D Y)}
variable {E'' : (letI := α; OrderAction D Z)}
variable {h : (letI := α; X.opens = Y.opens)}
variable {k : (letI := α; Y.opens = Z.opens)}

/-- Equal scalar structures identify the entire full-order rational centralizers. -/
def reAlgebra (β : Algebra O R) (e : α = β) :
    (letI := α; RationalHom F E E' h) ≃ₗ[F]
      (letI := β; RationalHom F (E.reAlgebra β e) (E'.reAlgebra β e)
        (reAlgebraOpens_eq X Y β e h)) := by
  cases e
  exact LinearEquiv.refl F _

/-- Forgetting the order retains the actual ambient tensor transport. -/
@[simp]
theorem reAlgebra_val (β : Algebra O R) (e : α = β)
    (q : (letI := α; RationalHom F E E' h)) :
    (letI := β; (reAlgebra β e q).val) =
      (letI := α; BasicAtlas.RationalHom.reAlgebra β e q.val) := by
  cases e
  rfl

/-- Transport retains rationalization of each actual integral full-order map. -/
@[simp]
theorem reAlgebra_ofHom (β : Algebra O R) (e : α = β)
    (g : (letI := α; Hom E E' h)) :
    reAlgebra β e (letI := α; ofHom (F := F) g) =
      (letI := β; ofHom (F := F) (g.reAlgebra β e)) := by
  cases e
  rfl

/-- Scalar transport preserves the actual full-order rational identity. -/
@[simp]
theorem reAlgebra_id (E : (letI := α; OrderAction D X))
    (β : Algebra O R) (e : α = β) :
    reAlgebra β e (letI := α; id (F := F) E) =
      (letI := β; id (F := F) (E.reAlgebra β e)) := by
  cases e
  rfl

/-- Scalar transport preserves actual full-order rational formal composition. -/
@[simp]
theorem reAlgebra_comp (β : Algebra O R) (e : α = β)
    (q : (letI := α; RationalHom F E' E'' k))
    (g : (letI := α; RationalHom F E E' h)) :
    reAlgebra β e (letI := α; q.comp g) =
      (letI := β; (reAlgebra β e q).comp (reAlgebra β e g)) := by
  cases e
  rfl

/-- Reflexive scalar transport is the identity on each full-order rational map. -/
@[simp]
theorem reAlgebra_refl (q : (letI := α; RationalHom F E E' h)) :
    reAlgebra α rfl q = q := rfl

end AlgebraTransport

variable [Algebra O R] [Algebra O S]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ} {Z : BasicAtlas O R υ}
variable {E : OrderAction D X} {E' : OrderAction D Y} {E'' : OrderAction D Z}
variable {h : X.opens = Y.opens} {k : Y.opens = Z.opens}

/-- Extend the full-order rational map to the supplied target scalar structure. -/
def baseChangeAlong (f : R →ₐ[O] S) :
    RationalHom F E E' h →ₗ[F]
      RationalHom F (E.baseChangeAlong f) (E'.baseChangeAlong f)
        (baseAlongOpens_eq X Y f h) :=
  (reAlgebra (F := F) (E := E.baseChange (coefficientTest f))
    (E' := E'.baseChange (coefficientTest f)) (h := baseOpens_eq (coefficientTest f) h)
      _ (coefficientAlgebraAlong_eq f)).toLinearMap.comp
        (baseChange (E := E) (E' := E') (h := h) (coefficientTest f))

/-- Forgetting order commutation recovers exactly supplied-target ambient extension. -/
@[simp]
theorem baseChangeAlong_val (f : R →ₐ[O] S) (q : RationalHom F E E' h) :
    (baseChangeAlong (E := E) (E' := E') (h := h) f q).val =
      BasicAtlas.RationalHom.baseChangeAlong (X := X) (Y := Y) (h := h) f q.val := by
  exact reAlgebra_val _ _ _

/-- Extension agrees with rationalization of the supplied-target integral map. -/
@[simp]
theorem baseChangeAlong_ofHom (f : R →ₐ[O] S) (g : Hom E E' h) :
    baseChangeAlong (E := E) (E' := E') (h := h) f (ofHom (F := F) g) =
      ofHom (F := F) (g.baseChangeAlong f) := by
  change reAlgebra _ _ (baseChange (coefficientTest f) (ofHom (F := F) g)) = _
  rw [baseChange_ofHom, reAlgebra_ofHom]
  rfl

/-- Supplied-target extension preserves the full-order rational identity. -/
@[simp]
theorem baseChangeAlong_id (E : OrderAction D X) (f : R →ₐ[O] S) :
    baseChangeAlong (E := E) (E' := E) (h := rfl) f (id (F := F) E) =
      id (E.baseChangeAlong f) := by
  change reAlgebra _ _ (baseChange (coefficientTest f) (id (F := F) E)) = _
  rw [baseChange_id, reAlgebra_id]
  rfl

/-- Supplied-target extension preserves actual full-order rational composition. -/
@[simp]
theorem baseChangeAlong_comp (q : RationalHom F E' E'' k) (g : RationalHom F E E' h)
    (f : R →ₐ[O] S) :
    baseChangeAlong (E := E) (E' := E'') (h := h.trans k) f (q.comp g) =
      (baseChangeAlong (E := E') (E' := E'') (h := k) f q).comp
        (baseChangeAlong (E := E) (E' := E') (h := h) f g) := by
  change reAlgebra _ _ (baseChange (coefficientTest f) (q.comp g)) = _
  rw [baseChange_comp, reAlgebra_comp]
  rfl

/-- Supplied-target extension is a ring map for full-order rational endomorphisms. -/
def baseChangeAlongRingHom (E : OrderAction D X) (f : R →ₐ[O] S) :
    RationalHom F E E rfl →+*
      RationalHom F (E.baseChangeAlong f) (E.baseChangeAlong f) rfl where
  toFun := baseChangeAlong (E := E) (E' := E) (h := rfl) f
  map_zero' := (baseChangeAlong (E := E) (E' := E) (h := rfl) f).map_zero
  map_add' := (baseChangeAlong (E := E) (E' := E) (h := rfl) f).map_add
  map_one' := baseChangeAlong_id E f
  map_mul' := fun q g => baseChangeAlong_comp q g f

end RationalHom

namespace QuasiIsogeny

variable [Algebra O R] [Algebra O S] [IsDomain O] [IsFractionRing O F]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ} {Z : BasicAtlas O R υ}
variable {E : OrderAction D X} {E' : OrderAction D Y} {E'' : OrderAction D Z}
variable {h : X.opens = Y.opens} {k : Y.opens = Z.opens}

/-- Extend both full-order rational maps, with both inverse equations, to supplied scalars. -/
def baseChangeAlong (g : QuasiIsogeny F E E' h) (f : R →ₐ[O] S) :
    QuasiIsogeny F (E.baseChangeAlong f) (E'.baseChangeAlong f)
      (baseOpens_eq (coefficientTest f) h) where
  hom := RationalHom.baseChangeAlong (E := E) (E' := E') (h := h) f g.hom
  inv := RationalHom.baseChangeAlong (E := E') (E' := E) (h := h.symm) f g.inv
  inv_hom := by
    rw [← RationalHom.baseChangeAlong_comp, g.inv_hom, RationalHom.baseChangeAlong_id]
  hom_inv := by
    rw [← RationalHom.baseChangeAlong_comp, g.hom_inv, RationalHom.baseChangeAlong_id]

@[simp]
theorem baseChangeAlong_hom (g : QuasiIsogeny F E E' h) (f : R →ₐ[O] S) :
    (g.baseChangeAlong f).hom =
      RationalHom.baseChangeAlong (E := E) (E' := E') (h := h) f g.hom := rfl

@[simp]
theorem baseChangeAlong_inv (g : QuasiIsogeny F E E' h) (f : R →ₐ[O] S) :
    (g.baseChangeAlong f).inv =
      RationalHom.baseChangeAlong (E := E') (E' := E) (h := h.symm) f g.inv := rfl

/-- Forgetting the order recovers precisely supplied-target ambient quasi-isogeny extension. -/
@[simp]
theorem toAtlas_baseChangeAlong (g : QuasiIsogeny F E E' h) (f : R →ₐ[O] S) :
    (g.baseChangeAlong f).toAtlasQuasiIsogeny = g.toAtlasQuasiIsogeny.baseChangeAlong f := by
  apply BasicAtlas.QuasiIsogeny.ext_hom
  exact RationalHom.baseChangeAlong_val f g.hom

@[simp]
theorem baseChangeAlong_refl (E : OrderAction D X) (f : R →ₐ[O] S) :
    (refl (F := F) E).baseChangeAlong f = refl (E.baseChangeAlong f) := by
  apply ext_hom
  exact RationalHom.baseChangeAlong_id E f

@[simp]
theorem baseChangeAlong_symm (g : QuasiIsogeny F E E' h) (f : R →ₐ[O] S) :
    g.symm.baseChangeAlong f = (g.baseChangeAlong f).symm := by
  apply ext_hom
  rfl

@[simp]
theorem baseChangeAlong_trans (g : QuasiIsogeny F E E' h) (q : QuasiIsogeny F E' E'' k)
    (f : R →ₐ[O] S) :
    (g.trans q).baseChangeAlong f = (g.baseChangeAlong f).trans (q.baseChangeAlong f) := by
  apply ext_hom
  exact RationalHom.baseChangeAlong_comp q.hom g.hom f

@[simp]
theorem baseChangeAlong_ofIso (g : Iso E E' h) (f : R →ₐ[O] S) :
    (ofIso (F := F) g).baseChangeAlong f = ofIso (g.baseChangeAlong f) := by
  apply ext_hom
  change RationalHom.baseChangeAlong f (RationalHom.ofHom (F := F) g.hom) =
    RationalHom.ofHom (g.baseChangeAlong f).hom
  rw [Iso.baseChangeAlong_hom]
  exact RationalHom.baseChangeAlong_ofHom f g.hom

end QuasiIsogeny

end OrderAction

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
