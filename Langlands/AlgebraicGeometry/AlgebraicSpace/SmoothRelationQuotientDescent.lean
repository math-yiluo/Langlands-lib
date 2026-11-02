import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotientStatement
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-! # Elementary descent through the canonical smooth-relation quotient -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotient

variable {S : Scheme.{u}} {U : Over S} (R : AlgebraicSpace S)
  (s t : R.presheaf ⟶ (schemeYoneda S).obj U)
  (h : IsEquivalenceRelation R s t)

/-- Equality in the pointwise quotient retains the full actual-arrow witness. -/
theorem toQuotientPresheaf_eq_iff (T : Over S)
    (x y : ((schemeYoneda S).obj U).obj (op T)) :
    (toQuotientPresheaf R s t h).app (op T) x =
        (toQuotientPresheaf R s t h).app (op T) y ↔ relation R s t T x y :=
  Quotient.eq

/-- Every section of the pointwise quotient has a representative. -/
theorem toQuotientPresheaf_surjective (T : Over S) :
    Function.Surjective ((toQuotientPresheaf R s t h).app (op T)) :=
  Quotient.mk_surjective

/-- The pointwise quotient identifies the two endpoints of every actual arrow. -/
theorem toQuotientPresheaf_coequalizes :
    s ≫ toQuotientPresheaf R s t h = t ≫ toQuotientPresheaf R s t h := by
  ext T r
  exact (toQuotientPresheaf_eq_iff R s t h T.unop _ _).mpr ⟨r, rfl, rfl⟩

/-- The complete arrow presheaf is the kernel pair before sheafification. -/
theorem isPullback_toQuotientPresheaf :
    IsPullback s t (toQuotientPresheaf R s t h) (toQuotientPresheaf R s t h) := by
  apply IsPullback.of_forall_isPullback_app
  intro T
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨congrArg (fun a => a.app T) (toQuotientPresheaf_coequalizes R s t h), ?_, ?_⟩
  · intro r r' hrr'
    exact (h T.unop).1 (Prod.ext hrr'.1 hrr'.2)
  · intro x y hxy
    exact (toQuotientPresheaf_eq_iff R s t h T.unop x y).mp hxy

variable {F : Presheaf S} (a : (schemeYoneda S).obj U ⟶ F)
  (ha : s ≫ a = t ≫ a)

/-- A map constant on actual relation arrows descends to all pointwise classes. -/
def quotientPresheafDesc : quotientPresheaf R s t h ⟶ F where
  app T := ↾(Quotient.lift (a.app T) (by
    intro x y hxy
    obtain ⟨r, rfl, rfl⟩ := hxy
    exact congrArg (fun b => b.app T r) ha))
  naturality T V g := by
    ext q
    induction q using Quotient.ind with
    | _ x => exact NatTrans.naturality_apply a g x

/-- The descended map recovers the given map on every scheme point. -/
@[simp]
theorem toQuotientPresheaf_desc :
    toQuotientPresheaf R s t h ≫ quotientPresheafDesc R s t h a ha = a := rfl

/-- A map out of the pointwise quotient is determined by all scheme points. -/
theorem quotientPresheaf_hom_ext {b c : quotientPresheaf R s t h ⟶ F}
    (hbc : toQuotientPresheaf R s t h ≫ b = toQuotientPresheaf R s t h ≫ c) :
    b = c := by
  ext T q
  obtain ⟨x, rfl⟩ := toQuotientPresheaf_surjective R s t h T.unop q
  exact congrArg (fun d => d.app T x) hbc

/-- The fixed etale quotient identifies the endpoints of every actual arrow. -/
theorem quotientMap_coequalizes :
    s ≫ quotientMap R s t h = t ≫ quotientMap R s t h := by
  exact congrArg (fun b => b ≫
    toSheafify (Scheme.etaleTopology.over S) (quotientPresheaf R s t h))
    (toQuotientPresheaf_coequalizes R s t h)

/-- A relation-constant map into an etale sheaf descends through the fixed
canonical etale quotient, including sections with only local representatives. -/
def quotientSheafDesc (hF : CategoryTheory.Presheaf.IsSheaf
    (Scheme.etaleTopology.over S) F) : (quotientSheaf R s t h).obj ⟶ F :=
  sheafifyLift (Scheme.etaleTopology.over S) (quotientPresheafDesc R s t h a ha) hF

/-- The etale descent map is compatible with the fixed canonical quotient map. -/
@[simp]
theorem quotientMap_desc (hF : CategoryTheory.Presheaf.IsSheaf
    (Scheme.etaleTopology.over S) F) :
    quotientMap R s t h ≫ quotientSheafDesc R s t h a ha hF = a := by
  change toQuotientPresheaf R s t h ≫
    (toSheafify (Scheme.etaleTopology.over S) (quotientPresheaf R s t h) ≫
      sheafifyLift (Scheme.etaleTopology.over S) (quotientPresheafDesc R s t h a ha) hF) = a
  rw [toSheafify_sheafifyLift]
  rfl

/-- Maps from the etale quotient to an etale sheaf are determined by their
composites with the fixed scheme presentation map. -/
theorem quotientSheaf_hom_ext (hF : CategoryTheory.Presheaf.IsSheaf
    (Scheme.etaleTopology.over S) F)
    {b c : (quotientSheaf R s t h).obj ⟶ F}
    (hbc : quotientMap R s t h ≫ b = quotientMap R s t h ≫ c) : b = c := by
  apply sheafify_hom_ext _ _ _ hF
  apply quotientPresheaf_hom_ext R s t h
  ext T x
  exact congrArg (fun d => d.app T x) hbc

end Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotient
