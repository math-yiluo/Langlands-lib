import Langlands.Geometry.FormalGroup.GlobalAtlasOrderBaseChange

/-! # Actual global-cover comparisons over supplied scalar structures -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ : Type} [Finite σ] {M : ModuleLaw O R σ}
variable (E : ModuleLaw.OrderAction D M) (s : Set R) (hs : Ideal.span s = ⊤)

section AlgebraTransport

variable (T : CommAlgCat.{v} R) (β : Algebra O T)
variable (e : coefficientAlgebra (O := O) T = β)
variable (f : (letI := β; R →ₐ[O] T)) (hf : f.toRingHom = algebraMap R T)

set_option backward.isDefEq.respectTransparency false in
/-- Retype both sides of the actual global-cover comparison to the specified scalar map. -/
def globalCoverBaseReAlgebraIso :
    (letI := β;
      OrderAction.Iso (((ofGlobalCoverOrderAction E s hs).baseChange T).reAlgebra β e)
        (ofGlobalCoverOrderAction (E.map f) ((ofGlobalCover M s hs).baseOpens T)
          ((ofGlobalCover M s hs).baseOpens_covers T)) rfl) := by
  cases e
  have he : f = IsScalarTower.toAlgHom O R T :=
    AlgHom.ext (fun x => RingHom.congr_fun hf x)
  cases he
  exact globalCoverBaseIso E s hs T

set_option backward.isDefEq.respectTransparency false in
/-- Scalar retyping retains the actual forward identity-coordinate formal map. -/
theorem globalCoverBaseReAlgebraIso_hom_coordinates
    (A : CommAlgCat.{v} T) (b : (ofGlobalCover M s hs).baseOpens T)
    (hb : IsUnit (algebraMap T A b.val)) :
    (letI := β;
      ((globalCoverBaseReAlgebraIso E s hs T β e f hf).hom.val.hom A b hb).toHom.toCoordinateMap) = CoordinateMap.id := by
  cases e
  have he : f = IsScalarTower.toAlgHom O R T :=
    AlgHom.ext (fun x => RingHom.congr_fun hf x)
  cases he
  exact globalCoverBaseChartIso_hom_coordinates E s hs T A b hb

set_option backward.isDefEq.respectTransparency false in
/-- Scalar retyping retains the actual inverse identity-coordinate formal map. -/
theorem globalCoverBaseReAlgebraIso_inv_coordinates
    (A : CommAlgCat.{v} T) (b : (ofGlobalCover M s hs).baseOpens T)
    (hb : IsUnit (algebraMap T A b.val)) :
    (letI := β;
      ((globalCoverBaseReAlgebraIso E s hs T β e f hf).inv.val.hom A b hb).toHom.toCoordinateMap) = CoordinateMap.id := by
  cases e
  have he : f = IsScalarTower.toAlgHom O R T :=
    AlgHom.ext (fun x => RingHom.congr_fun hf x)
  cases he
  exact globalCoverBaseChartIso_inv_coordinates E s hs T A b hb

end AlgebraTransport

variable {S : Type v} [CommRing S] [Algebra O S]

/-- Actual full-order maps compare supplied-target extension with the extended global cover. -/
def globalCoverBaseAlongIso (f : R →ₐ[O] S) :
    OrderAction.Iso ((ofGlobalCoverOrderAction E s hs).baseChangeAlong f)
      (ofGlobalCoverOrderAction (E.map f) (f '' s)
        ((ofGlobalCover M s hs).baseOpens_covers (coefficientTest f))) rfl :=
  globalCoverBaseReAlgebraIso E s hs (coefficientTest f) _
    (coefficientAlgebraAlong_eq f) f rfl

/-- The supplied forward comparison is the actual identity coordinate series. -/
theorem globalCoverBaseAlongIso_hom_coordinates (f : R →ₐ[O] S)
    (A : CommAlgCat.{v} S) (b : f '' s) (hb : IsUnit (algebraMap S A b.val)) :
    ((globalCoverBaseAlongIso E s hs f).hom.val.hom A b hb).toHom.toCoordinateMap =
      CoordinateMap.id :=
  globalCoverBaseReAlgebraIso_hom_coordinates E s hs (coefficientTest f) _
    (coefficientAlgebraAlong_eq f) f rfl A b hb

/-- The supplied inverse is the actual inverse formal map, also with identity series. -/
theorem globalCoverBaseAlongIso_inv_coordinates (f : R →ₐ[O] S)
    (A : CommAlgCat.{v} S) (b : f '' s) (hb : IsUnit (algebraMap S A b.val)) :
    ((globalCoverBaseAlongIso E s hs f).inv.val.hom A b hb).toHom.toCoordinateMap =
      CoordinateMap.id :=
  globalCoverBaseReAlgebraIso_inv_coordinates E s hs (coefficientTest f) _
    (coefficientAlgebraAlong_eq f) f rfl A b hb

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
