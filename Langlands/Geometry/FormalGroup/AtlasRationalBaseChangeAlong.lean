import Langlands.Geometry.FormalGroup.AtlasRationalBaseChange
import Langlands.Geometry.FormalGroup.AtlasBaseChangeAlong

/-! # Rational formal atlas maps over supplied scalar structures -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory TensorProduct

variable {O : Type u} [CommRing O]
variable {R S : Type v} [CommRing R] [CommRing S]
variable {F : Type w} [Field F] [Algebra O F]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]

attribute [local instance] coefficientAlgebra coefficientScalarTower

namespace RationalHom

section AlgebraTransport

variable {α : Algebra O R}
variable {X : @BasicAtlas O _ R _ α σ _}
variable {Y : @BasicAtlas O _ R _ α τ _}
variable {Z : @BasicAtlas O _ R _ α υ _}
variable {h : (letI := α; X.opens = Y.opens)} {k : (letI := α; Y.opens = Z.opens)}

/-- Equal scalar structures give an F-linear equivalence of actual global tensor Hom. -/
def reAlgebra (β : Algebra O R) (e : α = β) :
    (letI := α; RationalHom F X Y h) ≃ₗ[F]
      (letI := β; RationalHom F (X.reAlgebra β e) (Y.reAlgebra β e) h) := by
  cases e
  exact LinearEquiv.refl F _

/-- Transport retains the rationalization of each actual integral formal map. -/
@[simp]
theorem reAlgebra_ofHom (β : Algebra O R) (e : α = β)
    (g : (letI := α; Hom X Y h)) :
    reAlgebra β e (letI := α; ofHom (F := F) g) =
      (letI := β; ofHom (F := F) (g.reAlgebra β e)) := by
  cases e
  rfl

/-- Transport preserves the actual rational identity. -/
@[simp]
theorem reAlgebra_id (X : @BasicAtlas O _ R _ α σ _)
    (β : Algebra O R) (e : α = β) :
    reAlgebra β e (letI := α; id (F := F) X) =
      (letI := β; id (F := F) (X.reAlgebra β e)) := by
  cases e
  rfl

/-- Transport preserves actual rational formal composition. -/
@[simp]
theorem reAlgebra_comp (β : Algebra O R) (e : α = β)
    (q : (letI := α; RationalHom F Y Z k)) (g : (letI := α; RationalHom F X Y h)) :
    reAlgebra β e (letI := α; comp q g) =
      (letI := β; comp (reAlgebra β e q) (reAlgebra β e g)) := by
  cases e
  rfl

/-- Reflexive scalar transport acts as the identity on every rational formal map. -/
@[simp]
theorem reAlgebra_refl (g : (letI := α; RationalHom F X Y h)) :
    reAlgebra α rfl g = g := rfl

end AlgebraTransport

variable [Algebra O R] [Algebra O S]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ} {Z : BasicAtlas O R υ}
variable {h : X.opens = Y.opens} {k : Y.opens = Z.opens}

/-- Extend to the supplied target O-algebra, transporting the actual tensor Hom. -/
def baseChangeAlong (f : R →ₐ[O] S) :
    RationalHom F X Y h →ₗ[F]
      RationalHom F (X.baseChangeAlong f) (Y.baseChangeAlong f)
        (baseOpens_eq (coefficientTest f) h) :=
  (reAlgebra (F := F) (X := X.baseChange (coefficientTest f))
    (Y := Y.baseChange (coefficientTest f)) (h := baseOpens_eq (coefficientTest f) h)
      _ (coefficientAlgebraAlong_eq f)).toLinearMap.comp
        (baseChange (X := X) (Y := Y) (h := h) (coefficientTest f))

/-- Supplied-target extension retains rationalization of actual integral maps. -/
@[simp]
theorem baseChangeAlong_ofHom (f : R →ₐ[O] S) (g : Hom X Y h) :
    baseChangeAlong (X := X) (Y := Y) (h := h) f (ofHom (F := F) g) =
      ofHom (F := F) (g.baseChangeAlong f) := by
  change reAlgebra _ _ (baseChange (coefficientTest f) (ofHom (F := F) g)) = _
  rw [baseChange_ofHom, reAlgebra_ofHom]
  rfl

/-- Extension to a supplied target preserves the rational formal identity. -/
@[simp]
theorem baseChangeAlong_id (X : BasicAtlas O R σ) (f : R →ₐ[O] S) :
    baseChangeAlong (X := X) (Y := X) (h := rfl) f (id (F := F) X) =
      id (X.baseChangeAlong f) := by
  change reAlgebra _ _ (baseChange (coefficientTest f) (id (F := F) X)) = _
  rw [baseChange_id, reAlgebra_id]
  rfl

/-- Extension to a supplied target preserves actual rational formal composition. -/
@[simp]
theorem baseChangeAlong_comp (q : RationalHom F Y Z k) (g : RationalHom F X Y h)
    (f : R →ₐ[O] S) :
    baseChangeAlong (X := X) (Y := Z) (h := h.trans k) f (comp q g) =
      comp (baseChangeAlong (X := Y) (Y := Z) (h := k) f q)
        (baseChangeAlong (X := X) (Y := Y) (h := h) f g) := by
  change reAlgebra _ _ (baseChange (coefficientTest f) (comp q g)) = _
  rw [baseChange_comp, reAlgebra_comp]
  rfl

/-- Supplied-target extension is a ring map for rational endomorphism composition. -/
def baseChangeAlongRingHom (X : BasicAtlas O R σ) (f : R →ₐ[O] S) :
    RationalHom F X X rfl →+* RationalHom F (X.baseChangeAlong f) (X.baseChangeAlong f) rfl where
  toFun := baseChangeAlong (X := X) (Y := X) (h := rfl) f
  map_zero' := (baseChangeAlong (X := X) (Y := X) (h := rfl) f).map_zero
  map_add' := (baseChangeAlong (X := X) (Y := X) (h := rfl) f).map_add
  map_one' := baseChangeAlong_id X f
  map_mul' := fun q g => baseChangeAlong_comp q g f

end RationalHom

namespace QuasiIsogeny

variable [Algebra O R] [Algebra O S] [IsDomain O] [IsFractionRing O F]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ} {Z : BasicAtlas O R υ}
variable {h : X.opens = Y.opens} {k : Y.opens = Z.opens}

/-- Extend both rational maps to the supplied target and retain both inverse equations. -/
def baseChangeAlong (g : QuasiIsogeny F X Y h) (f : R →ₐ[O] S) :
    QuasiIsogeny F (X.baseChangeAlong f) (Y.baseChangeAlong f)
      (baseOpens_eq (coefficientTest f) h) where
  hom := RationalHom.baseChangeAlong (X := X) (Y := Y) (h := h) f g.hom
  inv := RationalHom.baseChangeAlong (X := Y) (Y := X) (h := h.symm) f g.inv
  inv_hom := by
    rw [← RationalHom.baseChangeAlong_comp, g.inv_hom, RationalHom.baseChangeAlong_id]
  hom_inv := by
    rw [← RationalHom.baseChangeAlong_comp, g.hom_inv, RationalHom.baseChangeAlong_id]

@[simp]
theorem baseChangeAlong_hom (g : QuasiIsogeny F X Y h) (f : R →ₐ[O] S) :
    (g.baseChangeAlong f).hom =
      RationalHom.baseChangeAlong (X := X) (Y := Y) (h := h) f g.hom := rfl

@[simp]
theorem baseChangeAlong_inv (g : QuasiIsogeny F X Y h) (f : R →ₐ[O] S) :
    (g.baseChangeAlong f).inv =
      RationalHom.baseChangeAlong (X := Y) (Y := X) (h := h.symm) f g.inv := rfl

@[simp]
theorem baseChangeAlong_refl (X : BasicAtlas O R σ) (f : R →ₐ[O] S) :
    (refl (F := F) X).baseChangeAlong f = refl (X.baseChangeAlong f) := by
  apply ext_hom
  exact RationalHom.baseChangeAlong_id X f

@[simp]
theorem baseChangeAlong_symm (g : QuasiIsogeny F X Y h) (f : R →ₐ[O] S) :
    g.symm.baseChangeAlong f = (g.baseChangeAlong f).symm := by
  apply ext_hom
  rfl

@[simp]
theorem baseChangeAlong_trans (g : QuasiIsogeny F X Y h) (q : QuasiIsogeny F Y Z k)
    (f : R →ₐ[O] S) :
    (g.trans q).baseChangeAlong f = (g.baseChangeAlong f).trans (q.baseChangeAlong f) := by
  apply ext_hom
  exact RationalHom.baseChangeAlong_comp q.hom g.hom f

@[simp]
theorem baseChangeAlong_ofIso (g : Iso X Y h) (f : R →ₐ[O] S) :
    (ofIso (F := F) g).baseChangeAlong f = ofIso (g.baseChangeAlong f) := by
  apply ext_hom
  exact (RationalHom.baseChangeAlong_ofHom f g.hom).trans
    (congrArg (RationalHom.ofHom (F := F))
      ((g.baseChange (coefficientTest f)).reAlgebra_hom _ (coefficientAlgebraAlong_eq f)).symm)

end QuasiIsogeny

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
