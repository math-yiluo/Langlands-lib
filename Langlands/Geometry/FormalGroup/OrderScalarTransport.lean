import Langlands.Geometry.FormalGroup.OrderQuasiIsogenyCalculus
import Langlands.Geometry.FormalGroup.AtlasAlgebraTransport

/-! # Actual formal maps under equality of scalar structures -/

noncomputable section

universe u v w z

namespace Langlands.FormalGroup.ModuleLaw

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] {α : Algebra O R}
variable {D : Type w} [Ring D] [Algebra O D]
variable {F : Type z} [Field F] [Algebra O F]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : (letI := α; ModuleLaw O R σ)}
variable {N : (letI := α; ModuleLaw O R τ)}
variable {P : (letI := α; ModuleLaw O R υ)}

/-- Equal scalar structures identify the actual integral formal Hom modules. -/
def Hom.reAlgebra (β : Algebra O R) (e : α = β) :
    (letI := α; Hom M N) ≃ₗ[O]
      (letI := β; Hom (M.reAlgebra β e) (N.reAlgebra β e)) := by
  cases e
  exact LinearEquiv.refl O _

/-- Retain both actual integral formal inverse maps through scalar retyping. -/
def Iso.reAlgebra (f : (letI := α; Iso M N)) (β : Algebra O R) (e : α = β) :
    (letI := β; Iso (M.reAlgebra β e) (N.reAlgebra β e)) := by
  cases e
  exact f

/-- Equal scalar structures identify the actual ambient rational tensor Hom modules. -/
def RationalHom.reAlgebra (β : Algebra O R) (e : α = β) :
    (letI := α; RationalHom F M N) ≃ₗ[F]
      (letI := β; RationalHom F (M.reAlgebra β e) (N.reAlgebra β e)) := by
  cases e
  exact LinearEquiv.refl F _

/-- Scalar transport retains rationalization of the specified actual formal map. -/
@[simp]
theorem RationalHom.reAlgebra_ofHom (β : Algebra O R) (e : α = β)
    (f : (letI := α; Hom M N)) :
    RationalHom.reAlgebra β e (letI := α; RationalHom.ofHom (F := F) f) =
      (letI := β; RationalHom.ofHom (F := F) (Hom.reAlgebra β e f)) := by
  cases e
  rfl

/-- Scalar transport preserves actual rational formal composition. -/
@[simp]
theorem RationalHom.reAlgebra_comp (β : Algebra O R) (e : α = β)
    (f : (letI := α; RationalHom F M N)) (g : (letI := α; RationalHom F N P)) :
    RationalHom.reAlgebra β e (letI := α; RationalHom.comp g f) =
      (letI := β; RationalHom.comp (RationalHom.reAlgebra β e g)
        (RationalHom.reAlgebra β e f)) := by
  cases e
  rfl

namespace OrderAction

variable {E : (letI := α; OrderAction D M)}
variable {E' : (letI := α; OrderAction D N)}
variable {E'' : (letI := α; OrderAction D P)}

/-- Retain the full actual order action on the same scalar-retyped formal module. -/
def reAlgebra (E : (letI := α; OrderAction D M)) (β : Algebra O R) (e : α = β) :
    (letI := β; OrderAction D (M.reAlgebra β e)) := by
  cases e
  exact E

/-- Retype an actual integral full-order formal map. -/
def Hom.reAlgebra (f : (letI := α; Hom E E')) (β : Algebra O R) (e : α = β) :
    (letI := β; Hom (E.reAlgebra β e) (E'.reAlgebra β e)) := by
  cases e
  exact f

/-- Retype the actual full-order formal isomorphism, including its inverse. -/
def Iso.reAlgebra (f : (letI := α; Iso E E')) (β : Algebra O R) (e : α = β) :
    (letI := β; Iso (E.reAlgebra β e) (E'.reAlgebra β e)) := by
  cases e
  exact f

/-- Scalar retyping commutes with forgetting the integral order condition. -/
@[simp]
theorem Hom.reAlgebra_val (f : (letI := α; Hom E E')) (β : Algebra O R) (e : α = β) :
    (letI := β; (f.reAlgebra β e).val) = ModuleLaw.Hom.reAlgebra β e f.val := by
  cases e
  rfl

/-- Equal scalar structures identify the whole actual rational full-order centralizers. -/
def RationalHom.reAlgebra (β : Algebra O R) (e : α = β) :
    (letI := α; RationalHom F E E') ≃ₗ[F]
      (letI := β; RationalHom F (E.reAlgebra β e) (E'.reAlgebra β e)) := by
  cases e
  exact LinearEquiv.refl F _

/-- Forgetting full-order commutation retains exactly the actual ambient tensor transport. -/
@[simp]
theorem RationalHom.reAlgebra_val (β : Algebra O R) (e : α = β)
    (f : (letI := α; RationalHom F E E')) :
    (letI := β; (RationalHom.reAlgebra β e f).val) =
      ModuleLaw.RationalHom.reAlgebra β e f.val := by
  cases e
  rfl

/-- Retyping preserves rationalization of the same integral full-order formal map. -/
@[simp]
theorem RationalHom.reAlgebra_ofHom (β : Algebra O R) (e : α = β)
    (f : (letI := α; Hom E E')) :
    RationalHom.reAlgebra β e (letI := α; RationalHom.ofHom (F := F) f) =
      (letI := β; RationalHom.ofHom (F := F) (f.reAlgebra β e)) := by
  cases e
  rfl

/-- Retyping preserves the full-order actual rational identity. -/
@[simp]
theorem RationalHom.reAlgebra_id (E : (letI := α; OrderAction D M))
    (β : Algebra O R) (e : α = β) :
    RationalHom.reAlgebra β e (letI := α; RationalHom.id (F := F) E) =
      (letI := β; RationalHom.id (F := F) (E.reAlgebra β e)) := by
  cases e
  rfl

/-- Retyping preserves actual full-order rational composition. -/
@[simp]
theorem RationalHom.reAlgebra_comp (β : Algebra O R) (e : α = β)
    (f : (letI := α; RationalHom F E E')) (g : (letI := α; RationalHom F E' E'')) :
    RationalHom.reAlgebra β e (letI := α; g.comp f) =
      (letI := β; (RationalHom.reAlgebra β e g).comp (RationalHom.reAlgebra β e f)) := by
  cases e
  rfl

namespace QuasiIsogeny

variable [IsDomain O] [IsFractionRing O F]

/-- Retain both actual rational full-order maps and inverse equations through scalar retyping. -/
def reAlgebra (f : (letI := α; QuasiIsogeny F E E')) (β : Algebra O R) (e : α = β) :
    (letI := β; QuasiIsogeny F (E.reAlgebra β e) (E'.reAlgebra β e)) := by
  cases e
  exact f

@[simp]
theorem reAlgebra_hom (f : (letI := α; QuasiIsogeny F E E'))
    (β : Algebra O R) (e : α = β) :
    (letI := β; (f.reAlgebra β e).hom) = RationalHom.reAlgebra β e (letI := α; f.hom) := by
  cases e
  rfl

@[simp]
theorem reAlgebra_inv (f : (letI := α; QuasiIsogeny F E E'))
    (β : Algebra O R) (e : α = β) :
    (letI := β; (f.reAlgebra β e).inv) = RationalHom.reAlgebra β e (letI := α; f.inv) := by
  cases e
  rfl

@[simp]
theorem reAlgebra_ofIso (f : (letI := α; Iso E E')) (β : Algebra O R) (e : α = β) :
    (letI := α; (ofIso (F := F) f).reAlgebra β e) =
      (letI := β; ofIso (F := F) (f.reAlgebra β e)) := by
  cases e
  rfl

@[simp]
theorem reAlgebra_symm (f : (letI := α; QuasiIsogeny F E E'))
    (β : Algebra O R) (e : α = β) :
    (letI := α; f.symm.reAlgebra β e) = (letI := β; (f.reAlgebra β e).symm) := by
  cases e
  rfl

@[simp]
theorem reAlgebra_trans (f : (letI := α; QuasiIsogeny F E E'))
    (g : (letI := α; QuasiIsogeny F E' E'')) (β : Algebra O R) (e : α = β) :
    (letI := α; (f.trans g).reAlgebra β e) =
      (letI := β; (f.reAlgebra β e).trans (g.reAlgebra β e)) := by
  cases e
  rfl

end QuasiIsogeny

end OrderAction

end Langlands.FormalGroup.ModuleLaw
