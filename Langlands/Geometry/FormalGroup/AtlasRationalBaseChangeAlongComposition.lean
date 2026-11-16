import Langlands.Geometry.FormalGroup.AtlasRationalBaseChangeComposition
import Langlands.Geometry.FormalGroup.AtlasRationalBaseChangeAlong
import Langlands.Geometry.FormalGroup.AtlasBaseChangeAlongComposition

/-! # Natural rational comparison of successive supplied coefficient maps -/

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

/-- Intermediate and final scalar transport preserve equality of successive covers. -/
theorem baseCompReAlgebraMapOpens_eq
    (X : BasicAtlas O R σ) (Y : BasicAtlas O R τ)
    (S : CommAlgCat.{v} R) (T : CommAlgCat.{v} S)
    (β : Algebra O S) (e : coefficientAlgebra (O := O) S = β)
    (γ : Algebra O T) (d : (letI := β; coefficientAlgebra (O := O) T) = γ)
    (h : X.opens = Y.opens) :
    (letI := γ;
      ((letI := β; ((X.baseChange S).reAlgebra β e).baseChange T).reAlgebra γ d).opens =
        ((letI := β; ((Y.baseChange S).reAlgebra β e).baseChange T).reAlgebra γ d).opens) := by
  cases e
  cases d
  exact baseOpens_eq T (baseOpens_eq S h)

namespace Hom

/-- Retyping both bases preserves naturality of the actual integral comparison. -/
theorem baseCompReAlgebra_natural (q : Hom X Y h)
    (S : CommAlgCat.{v} R) (T : CommAlgCat.{v} S)
    (β : Algebra O S) (e : coefficientAlgebra (O := O) S = β)
    (γ : Algebra O T) (d : (letI := β; coefficientAlgebra (O := O) T) = γ) :
    (letI := γ;
      (Y.baseCompReAlgebraIso S T β e γ d).hom.comp
        (h := baseCompReAlgebraMapOpens_eq X Y S T β e γ d h)
        ((letI := β; ((q.baseChange S).reAlgebra β e).baseChange T).reAlgebra γ d)) =
      (letI := γ;
        ((q.baseChange (restrictTest S T)).reAlgebra γ
          ((coefficientAlgebra_comp_transport S T β e).trans d)).comp
            (X.baseCompReAlgebraIso S T β e γ d).hom) := by
  cases e
  cases d
  exact q.baseComp_natural S T

/-- The reverse actual comparison is natural after the same two scalar transports. -/
theorem baseCompReAlgebra_inv_natural (q : Hom X Y h)
    (S : CommAlgCat.{v} R) (T : CommAlgCat.{v} S)
    (β : Algebra O S) (e : coefficientAlgebra (O := O) S = β)
    (γ : Algebra O T) (d : (letI := β; coefficientAlgebra (O := O) T) = γ) :
    (letI := γ;
      ((letI := β; ((q.baseChange S).reAlgebra β e).baseChange T).reAlgebra γ d).comp
        (k := baseCompReAlgebraMapOpens_eq X Y S T β e γ d h)
        (X.baseCompReAlgebraIso S T β e γ d).inv) =
      (letI := γ;
        (Y.baseCompReAlgebraIso S T β e γ d).inv.comp
          ((q.baseChange (restrictTest S T)).reAlgebra γ
            ((coefficientAlgebra_comp_transport S T β e).trans d))) := by
  cases e
  cases d
  exact q.baseComp_inv_natural S T

end Hom

namespace RationalHom

/-- The full global tensor naturality equation survives both scalar transports. -/
theorem baseCompReAlgebra_natural (q : RationalHom F X Y h)
    (S : CommAlgCat.{v} R) (T : CommAlgCat.{v} S)
    (β : Algebra O S) (e : coefficientAlgebra (O := O) S = β)
    (γ : Algebra O T) (d : (letI := β; coefficientAlgebra (O := O) T) = γ) :
    (letI := γ;
      comp (h := baseCompReAlgebraMapOpens_eq X Y S T β e γ d h)
        (ofHom (F := F) (Y.baseCompReAlgebraIso S T β e γ d).hom)
        (letI := β;
          reAlgebra γ d
            (baseChange (X := (X.baseChange S).reAlgebra β e)
              (Y := (Y.baseChange S).reAlgebra β e) (h := baseOpens_eq S h) T
              (reAlgebra β e (baseChange (X := X) (Y := Y) (h := h) S q))))) =
      (letI := γ;
        comp (reAlgebra γ ((coefficientAlgebra_comp_transport S T β e).trans d)
          (baseChange (X := X) (Y := Y) (h := h) (restrictTest S T) q))
          (ofHom (X.baseCompReAlgebraIso S T β e γ d).hom)) := by
  cases e
  cases d
  exact baseComp_natural q S T

/-- The reverse global tensor equation survives the same two scalar transports. -/
theorem baseCompReAlgebra_inv_natural (q : RationalHom F X Y h)
    (S : CommAlgCat.{v} R) (T : CommAlgCat.{v} S)
    (β : Algebra O S) (e : coefficientAlgebra (O := O) S = β)
    (γ : Algebra O T) (d : (letI := β; coefficientAlgebra (O := O) T) = γ) :
    (letI := γ;
      comp (k := baseCompReAlgebraMapOpens_eq X Y S T β e γ d h)
        (letI := β;
          reAlgebra γ d
            (baseChange (X := (X.baseChange S).reAlgebra β e)
              (Y := (Y.baseChange S).reAlgebra β e) (h := baseOpens_eq S h) T
              (reAlgebra β e (baseChange (X := X) (Y := Y) (h := h) S q))))
        (ofHom (F := F) (X.baseCompReAlgebraIso S T β e γ d).inv)) =
      (letI := γ;
        comp (ofHom (Y.baseCompReAlgebraIso S T β e γ d).inv)
          (reAlgebra γ ((coefficientAlgebra_comp_transport S T β e).trans d)
            (baseChange (X := X) (Y := Y) (h := h) (restrictTest S T) q))) := by
  cases e
  cases d
  exact baseComp_inv_natural q S T

end RationalHom

variable {S T : Type v} [CommRing S] [CommRing T] [Algebra O S] [Algebra O T]

/-- Equal original covers stay equal after two supplied coefficient maps. -/
theorem baseAlongCompMapOpens_eq
    (X : BasicAtlas O R σ) (Y : BasicAtlas O R τ)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) (h : X.opens = Y.opens) :
    ((X.baseChangeAlong f).baseChangeAlong g).opens =
      ((Y.baseChangeAlong f).baseChangeAlong g).opens :=
  baseCompReAlgebraMapOpens_eq X Y (coefficientTest f) (coefficientTest g) _
    (coefficientAlgebraAlong_eq f) _ (coefficientAlgebraAlong_eq g) h

namespace Hom

/-- The actual supplied-map composition comparison is natural in integral formal maps. -/
theorem baseAlongComp_natural (q : Hom X Y h) (f : R →ₐ[O] S) (g : S →ₐ[O] T) :
    (Y.baseAlongCompIso f g).hom.comp
        (h := baseAlongCompMapOpens_eq X Y f g h)
        ((q.baseChangeAlong f).baseChangeAlong g) =
      (q.baseChangeAlong (g.comp f)).comp (X.baseAlongCompIso f g).hom :=
  q.baseCompReAlgebra_natural (coefficientTest f) (coefficientTest g) _
    (coefficientAlgebraAlong_eq f) _ (coefficientAlgebraAlong_eq g)

/-- The inverse supplied-map composition comparison gives the reverse integral square. -/
theorem baseAlongComp_inv_natural (q : Hom X Y h) (f : R →ₐ[O] S) (g : S →ₐ[O] T) :
    ((q.baseChangeAlong f).baseChangeAlong g).comp
        (k := baseAlongCompMapOpens_eq X Y f g h) (X.baseAlongCompIso f g).inv =
      (Y.baseAlongCompIso f g).inv.comp (q.baseChangeAlong (g.comp f)) :=
  q.baseCompReAlgebra_inv_natural (coefficientTest f) (coefficientTest g) _
    (coefficientAlgebraAlong_eq f) _ (coefficientAlgebraAlong_eq g)

end Hom

namespace RationalHom

/-- Supplied-map composition is natural on the entire global tensor Hom. -/
theorem baseAlongComp_natural (q : RationalHom F X Y h)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) :
    comp (h := baseAlongCompMapOpens_eq X Y f g h)
      (ofHom (F := F) (Y.baseAlongCompIso f g).hom)
      (baseChangeAlong (X := X.baseChangeAlong f) (Y := Y.baseChangeAlong f)
        (h := baseOpens_eq (coefficientTest f) h) g
        (baseChangeAlong (X := X) (Y := Y) (h := h) f q)) =
      comp (baseChangeAlong (X := X) (Y := Y) (h := h) (g.comp f) q)
        (ofHom (X.baseAlongCompIso f g).hom) :=
  baseCompReAlgebra_natural q (coefficientTest f) (coefficientTest g) _
    (coefficientAlgebraAlong_eq f) _ (coefficientAlgebraAlong_eq g)

/-- The actual reverse comparison gives the reverse supplied-map rational square. -/
theorem baseAlongComp_inv_natural (q : RationalHom F X Y h)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) :
    comp (k := baseAlongCompMapOpens_eq X Y f g h)
      (baseChangeAlong (X := X.baseChangeAlong f) (Y := Y.baseChangeAlong f)
        (h := baseOpens_eq (coefficientTest f) h) g
        (baseChangeAlong (X := X) (Y := Y) (h := h) f q))
      (ofHom (F := F) (X.baseAlongCompIso f g).inv) =
      comp (ofHom (Y.baseAlongCompIso f g).inv)
        (baseChangeAlong (X := X) (Y := Y) (h := h) (g.comp f) q) :=
  baseCompReAlgebra_inv_natural q (coefficientTest f) (coefficientTest g) _
    (coefficientAlgebraAlong_eq f) _ (coefficientAlgebraAlong_eq g)

end RationalHom

section FractionField

variable [IsDomain O] [IsFractionRing O F]

/-- Rationalize the actual comparison for two supplied coefficient maps. -/
def baseAlongCompQuasiIsogeny (X : BasicAtlas O R σ)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) :
    QuasiIsogeny F ((X.baseChangeAlong f).baseChangeAlong g)
      (X.baseChangeAlong (g.comp f)) (X.baseAlongCompOpens_eq f g) :=
  QuasiIsogeny.ofIso (X.baseAlongCompIso f g)

@[simp]
theorem baseAlongCompQuasiIsogeny_hom (X : BasicAtlas O R σ)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) :
    (X.baseAlongCompQuasiIsogeny (F := F) f g).hom =
      RationalHom.ofHom (X.baseAlongCompIso f g).hom := rfl

@[simp]
theorem baseAlongCompQuasiIsogeny_inv (X : BasicAtlas O R σ)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) :
    (X.baseAlongCompQuasiIsogeny (F := F) f g).inv =
      RationalHom.ofHom (X.baseAlongCompIso f g).inv := rfl

namespace QuasiIsogeny

/-- Successive supplied extension commutes with the actual rational comparison. -/
theorem baseAlongComp_natural (q : QuasiIsogeny F X Y h)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) :
    ((q.baseChangeAlong f).baseChangeAlong g).trans
        (h := baseAlongCompMapOpens_eq X Y f g h) (Y.baseAlongCompQuasiIsogeny f g) =
      (X.baseAlongCompQuasiIsogeny f g).trans (q.baseChangeAlong (g.comp f)) := by
  apply ext_hom
  exact RationalHom.baseAlongComp_natural q.hom f g

/-- The actual inverse comparison gives the reverse supplied quasi-isogeny square. -/
theorem baseAlongComp_inv_natural (q : QuasiIsogeny F X Y h)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) :
    (X.baseAlongCompQuasiIsogeny f g).symm.trans
        (k := baseAlongCompMapOpens_eq X Y f g h)
        ((q.baseChangeAlong f).baseChangeAlong g) =
      (q.baseChangeAlong (g.comp f)).trans (Y.baseAlongCompQuasiIsogeny f g).symm := by
  apply ext_hom
  exact RationalHom.baseAlongComp_inv_natural q.hom f g

end QuasiIsogeny

end FractionField

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
