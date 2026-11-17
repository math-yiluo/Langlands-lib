import Langlands.GroupScheme.OuterIsomorphismSheafQuotient
import Langlands.AlgebraicGeometry.AlgebraicSpace.ExtensionProduct
import Langlands.AlgebraicGeometry.AlgebraicSpace.FppfQuotientRepresentability
import Mathlib.CategoryTheory.Sites.Limits

/-! # The canonical fppf quotient and its local scheme models -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SchemeAction

open Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {A : GroupScheme S} {X : Over S}
  (b : SchemeAction A X)

/-- The canonical quotient in actual fppf sheaves. -/
def quotientSheaf : FppfSheaf S :=
  coequalizer ((schemeSheaf S).map b.hom) ((schemeSheaf S).map (snd A.X X))

/-- The canonical morphism to the quotient sheaf. -/
def quotientMap : (schemeSheaf S).obj X ⟶ b.quotientSheaf :=
  coequalizer.π _ _

theorem quotientMap_isFppfActionQuotient :
    IsFppfActionQuotient b b.quotientMap :=
  ⟨coequalizer.condition _ _, ⟨coequalizerIsCoequalizer _ _⟩⟩

/-- The canonical quotient has local representatives on an fppf cover. -/
theorem quotientMap_isLocallySurjective :
    CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S) b.quotientMap.hom := by
  change Sheaf.IsLocallySurjective b.quotientMap
  apply (Sheaf.isLocallySurjective_iff_epi _).mpr
  change Epi (coequalizer.π _ _)
  infer_instance

/-- The quotient map is invariant under the action on every test. -/
theorem quotientMap_act {T : Over S} (d : T ⟶ A.X) (p : T ⟶ X) :
    b.quotientMap.hom.app (op T) ⟨b.act d p⟩ =
      b.quotientMap.hom.app (op T) ⟨p⟩ := by
  have h := congrArg
    (fun k => k.hom.app (op T) (⟨lift d p⟩ :
      ((schemeYoneda S).obj (A.X ⊗ X)).obj (op T)))
    b.quotientMap_isFppfActionQuotient.choose
  change b.quotientMap.hom.app (op T) ⟨b.act d p⟩ =
    b.quotientMap.hom.app (op T) ⟨(lift d p ≫ snd A.X X)⟩ at h
  simpa only [lift_snd] using h

/-- For a free action, equality in the quotient is an actual orbit equation
on the original test scheme. -/
theorem quotientMap_eq_iff
    (hfree : ∀ (T : Over S) (p : T ⟶ X),
      Function.Injective (fun d : T ⟶ A.X => b.act d p))
    {T : Over S} (p q : T ⟶ X) :
    b.quotientMap.hom.app (op T) ⟨p⟩ =
        b.quotientMap.hom.app (op T) ⟨q⟩ ↔
      ∃ d : T ⟶ A.X, b.act d p = q := by
  constructor
  · intro h
    exact (b.existsUnique_act_of_isFppfActionQuotient hfree
      b.quotientMap_isFppfActionQuotient p q h).exists
  · rintro ⟨d, rfl⟩
    exact (b.quotientMap_act d p).symm

/-- The quotient sheaf with an additional relative scheme parameter. -/
def quotientWithParameter (U : Over S) : FppfSheaf S :=
  ⟨extProd b.quotientSheaf.obj U, extProd.isSheaf b.quotientSheaf.property⟩

/-- The presentation of the quotient with parameter by `X × U`. -/
def quotientMapWithParameter (U : Over S) :
    (schemeYoneda S).obj (X ⨯ U) ⟶ (b.quotientWithParameter U).obj :=
  FunctorToTypes.prod.lift
    ((schemeYoneda S).map prod.fst ≫ b.quotientMap.hom)
    ((schemeYoneda S).map prod.snd)

/-- Adding a scheme parameter preserves local surjectivity of the quotient
presentation. -/
theorem quotientMapWithParameter_isLocallySurjective (U : Over S) :
    CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S)
      (b.quotientMapWithParameter U) := by
  let := b.quotientMap_isLocallySurjective
  constructor
  intro T z
  apply (fppfTopology S).superset_covering ?_
    (CategoryTheory.Presheaf.imageSieve_mem (fppfTopology S) b.quotientMap.hom z.1)
  rintro V f ⟨⟨p⟩, hp⟩
  refine ⟨⟨prod.lift p (f ≫ z.2.down)⟩, ?_⟩
  apply Prod.ext
  · change b.quotientMap.hom.app (op V)
      ⟨prod.lift p (f ≫ z.2.down) ≫ prod.fst⟩ =
        b.quotientSheaf.obj.map f.op z.1
    simpa only [prod.lift_fst] using hp
  · change (⟨prod.lift p (f ≫ z.2.down) ≫ prod.snd⟩ :
      ((schemeYoneda S).obj U).obj (op V)) = ⟨f ≫ z.2.down⟩
    rw [prod.lift_snd]

/-- A free action has the same kernel, with a parameter, as equality of the
parameter and an actual orbit equation. -/
theorem quotientMapWithParameter_eq_iff
    (hfree : ∀ (T : Over S) (p : T ⟶ X),
      Function.Injective (fun d : T ⟶ A.X => b.act d p))
    (U : Over S) {T : Over S} (p q : T ⟶ X ⨯ U) :
    (b.quotientMapWithParameter U).app (op T) ⟨p⟩ =
        (b.quotientMapWithParameter U).app (op T) ⟨q⟩ ↔
      p ≫ prod.snd = q ≫ prod.snd ∧
        ∃ d : T ⟶ A.X, b.act d (p ≫ prod.fst) = q ≫ prod.fst := by
  change (b.quotientMap.hom.app (op T) ⟨p ≫ prod.fst⟩,
      (ULift.up (p ≫ prod.snd) : ((schemeYoneda S).obj U).obj (op T))) =
    (b.quotientMap.hom.app (op T) ⟨q ≫ prod.fst⟩,
      (ULift.up (q ≫ prod.snd) : ((schemeYoneda S).obj U).obj (op T))) ↔ _
  rw [Prod.mk.injEq, b.quotientMap_eq_iff hfree]
  constructor
  · rintro ⟨hd, ht⟩
    exact ⟨congrArg ULift.down ht, hd⟩
  · rintro ⟨ht, hd⟩
    exact ⟨hd, congrArg ULift.up ht⟩

/-- Any local scheme quotient with the exact orbit kernel represents the
canonical quotient sheaf with the same parameter. -/
theorem exists_iso_quotientWithParameter
    (hfree : ∀ (T : Over S) (p : T ⟶ X),
      Function.Injective (fun d : T ⟶ A.X => b.act d p))
    (U M : Over S) (q : X ⨯ U ⟶ M)
    [Flat q.left] [LocallyOfFinitePresentation q.left] [Surjective q.left]
    (hker : ∀ (T : Over S) (p p' : T ⟶ X ⨯ U),
      p ≫ q = p' ≫ q ↔ p ≫ prod.snd = p' ≫ prod.snd ∧
        ∃ d : T ⟶ A.X, b.act d (p ≫ prod.fst) = p' ≫ prod.fst) :
    ∃ e : (schemeYoneda S).obj M ≅ (b.quotientWithParameter U).obj,
      (schemeYoneda S).map q ≫ e.hom = b.quotientMapWithParameter U := by
  apply exists_iso_of_locallySurjective_of_same_kernel
    (b.quotientMapWithParameter U) q
    (b.quotientMapWithParameter_isLocallySurjective U)
    (isLocallySurjective_schemeYoneda_map q)
  intro T p p'
  exact (b.quotientMapWithParameter_eq_iff hfree U p p').trans (hker T p p').symm

end Langlands.GroupScheme.SchemeAction
