import Langlands.Geometry.FormalGroup.AtlasOrderReductionUnit
import Langlands.Geometry.FormalGroup.AtlasOrderQuasiIsogenyCalculus

/-! # Whole rational atlas maps under a proved identity coefficient map -/

noncomputable section

universe u v w z

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

open CategoryTheory

variable {O : Type u} [CommRing O] [IsDomain O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {F : Type z} [Field F] [Algebra O F] [IsFractionRing O F]
variable {σ τ υ ω : Type} [Finite σ] [Finite τ] [Finite υ] [Finite ω]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {Z : BasicAtlas O R υ} {W : BasicAtlas O R ω}
variable {E : OrderAction D X} {E' : OrderAction D Y}
variable {E'' : OrderAction D Z} {E''' : OrderAction D W}
variable {h : X.opens = Y.opens} {k : Y.opens = Z.opens} {l : Z.opens = W.opens}

attribute [local instance] coefficientAlgebra coefficientScalarTower

namespace QuasiIsogeny

/-- The actual global tensor identity on the source is a composition unit. -/
@[simp]
theorem refl_trans (f : QuasiIsogeny F E E' h) : (refl E).trans f = f := by
  apply ext_hom
  exact RationalHom.comp_id f.hom

/-- The actual global tensor identity on the target is a composition unit. -/
@[simp]
theorem trans_refl (f : QuasiIsogeny F E E' h) : f.trans (refl E') = f := by
  apply ext_hom
  exact RationalHom.id_comp f.hom

/-- Associativity holds in the whole actual global rational full-order Hom. -/
theorem trans_assoc (f : QuasiIsogeny F E E' h) (g : QuasiIsogeny F E' E'' k)
    (q : QuasiIsogeny F E'' E''' l) : (f.trans g).trans q = f.trans (g.trans q) := by
  apply ext_hom
  exact (RationalHom.comp_assoc q.hom g.hom f.hom).symm

/-- The actual forward and inverse global tensor maps cancel. -/
@[simp]
theorem self_trans_symm (f : QuasiIsogeny F E E' h) : f.trans f.symm = refl E := by
  apply ext_hom
  exact f.inv_hom

/-- The actual inverse and forward global tensor maps cancel. -/
@[simp]
theorem symm_trans_self (f : QuasiIsogeny F E E' h) : f.symm.trans f = refl E' := by
  apply ext_hom
  exact f.hom_inv

/-- Cancel the same specified actual global tensor map on the right. -/
theorem trans_right_cancel (f g : QuasiIsogeny F E E' h) (q : QuasiIsogeny F E' E'' k)
    (e : f.trans q = g.trans q) : f = g := by
  have t := congrArg (fun z => z.trans q.symm) e
  simpa only [trans_assoc, self_trans_symm, trans_refl] using t

/-- Cancel the same specified actual global tensor map on the left. -/
theorem trans_left_cancel (f : QuasiIsogeny F E E' h) (g q : QuasiIsogeny F E' E'' k)
    (e : f.trans g = f.trans q) : g = q := by
  have t := congrArg (fun z => f.symm.trans z) e
  simpa only [← trans_assoc, symm_trans_self, refl_trans] using t

end QuasiIsogeny

/-- The actual integral map from extension by a proved identity coefficient map to the original atlas. -/
def identityAlongIso (E : OrderAction D X) {m : R →ₐ[O] R} (hm : m = AlgHom.id O R) :=
  (E.baseAlongEqIso hm).trans E.baseIdIso

/-- Rationalize both actual inverse maps of the proved-identity coefficient comparison. -/
def identityAlongQuasiIsogeny (E : OrderAction D X) {m : R →ₐ[O] R} (hm : m = AlgHom.id O R) :=
  QuasiIsogeny.ofIso (F := F) (E.identityAlongIso hm)

namespace QuasiIsogeny

/-- Proved-identity coefficient extension is natural on the whole actual global quasi-isogeny. -/
theorem identityAlong_natural (a : QuasiIsogeny F E E' h) {m : R →ₐ[O] R}
    (hm : m = AlgHom.id O R) :
    (a.baseChangeAlong m).trans (h := baseAlongOpens_eq X Y m h)
        (E'.identityAlongQuasiIsogeny (F := F) hm) =
      (E.identityAlongQuasiIsogeny (F := F) hm).trans a := by
  cases hm
  simpa only [identityAlongQuasiIsogeny, identityAlongIso, baseAlongEqIso,
    Iso.refl_trans, baseIdQuasiIsogeny] using a.baseId_natural

end QuasiIsogeny

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction
