import Langlands.Representation.Filtration.Definitions

/-! Natural descent and first isomorphism for actual subfunctor quotients. -/

noncomputable section
open CategoryTheory

namespace Langlands.RepSubfunctor

universe uR uG uV uC vC

variable {R : Type uR} [CommRing R] {G : Type uG} [Monoid G]
  {C : Type uC} [Category.{vC} C] {F H : C ⥤ Rep.{uV} R G}
  (S T : RepSubfunctor F)

/-- Descend a natural map on the upper subfunctor which kills the actual
pulled-back lower subrepresentation. -/
def quotientNatLift (α : T.toFunctor ⟶ H)
    (h : ∀ (X : C) (v : T.representation X),
      v ∈ S.lowerInUpper T X → (α.app X).hom v = 0) :
    S.quotientFunctor T ⟶ H where
  app X := Rep.ofHom
    { toLinearMap := (S.lowerInUpper T X).toSubmodule.liftQ
        (α.app X).hom.toLinearMap (h X)
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro v
        obtain ⟨v, rfl⟩ := S.quotientProjection_surjective T X v
        change (α.app X).hom ((T.representation X).ρ g v) =
          (H.obj X).ρ g ((α.app X).hom v)
        exact Rep.hom_comm_apply (α.app X) g v }
  naturality := by
    intro X Y f
    ext v
    obtain ⟨v, rfl⟩ := S.quotientProjection_surjective T X v
    exact congrArg (fun k => k.hom v) (α.naturality f)

@[simp]
theorem quotientNatLift_projection (α : T.toFunctor ⟶ H)
    (h : ∀ (X : C) (v : T.representation X),
      v ∈ S.lowerInUpper T X → (α.app X).hom v = 0)
    (X : C) (v : T.representation X) :
    ((S.quotientNatLift T α h).app X).hom
        ((S.quotientProjection T X).hom v) = (α.app X).hom v := rfl

/-- The descended map factors the original map through the natural projection. -/
theorem quotientNatProjection_lift (α : T.toFunctor ⟶ H)
    (h : ∀ (X : C) (v : T.representation X),
      v ∈ S.lowerInUpper T X → (α.app X).hom v = 0) :
    S.quotientNatProjection T ≫ S.quotientNatLift T α h = α := rfl

/-- Surjectivity of the canonical projection determines every natural descent. -/
theorem quotientNatLift_unique (α : T.toFunctor ⟶ H)
    (h : ∀ (X : C) (v : T.representation X),
      v ∈ S.lowerInUpper T X → (α.app X).hom v = 0)
    (β : S.quotientFunctor T ⟶ H)
    (hβ : S.quotientNatProjection T ≫ β = α) :
    β = S.quotientNatLift T α h := by
  ext X v
  obtain ⟨v, rfl⟩ := S.quotientProjection_surjective T X v
  exact congrArg (fun k => (k.app X).hom v) hβ

/-- An objectwise surjection with exactly the specified kernel induces
bijective components on the existing quotient functor. -/
theorem quotientNatLift_bijective (α : T.toFunctor ⟶ H)
    (hker : ∀ (X : C) (v : T.representation X),
      v ∈ S.lowerInUpper T X ↔ (α.app X).hom v = 0)
    (hsurj : ∀ X, Function.Surjective (α.app X).hom) (X : C) :
    Function.Bijective
      ((S.quotientNatLift T α (fun X v => (hker X v).mp)).app X).hom := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    exact Submodule.ker_liftQ_eq_bot _ _ _ (fun v hv => (hker X v).mpr hv)
  · intro v
    obtain ⟨w, rfl⟩ := hsurj X v
    exact ⟨(S.quotientProjection T X).hom w, rfl⟩

/-- The first isomorphism theorem for the actual successive quotient functor.
No containment of the lower subfunctor in the upper one is required. -/
def quotientNatIsoOfSurjective (α : T.toFunctor ⟶ H)
    (hker : ∀ (X : C) (v : T.representation X),
      v ∈ S.lowerInUpper T X ↔ (α.app X).hom v = 0)
    (hsurj : ∀ X, Function.Surjective (α.app X).hom) :
    S.quotientFunctor T ≅ H :=
  NatIso.ofComponents
    (fun X => Rep.mkIso
      (((S.quotientNatLift T α (fun X v => (hker X v).mp)).app X).hom.ofBijective
        (S.quotientNatLift_bijective T α hker hsurj X)))
    (fun f => (S.quotientNatLift T α (fun X v => (hker X v).mp)).naturality f)

@[simp]
theorem quotientNatIsoOfSurjective_hom_projection (α : T.toFunctor ⟶ H)
    (hker : ∀ (X : C) (v : T.representation X),
      v ∈ S.lowerInUpper T X ↔ (α.app X).hom v = 0)
    (hsurj : ∀ X, Function.Surjective (α.app X).hom)
    (X : C) (v : T.representation X) :
    ((S.quotientNatIsoOfSurjective T α hker hsurj).hom.app X).hom
        ((S.quotientProjection T X).hom v) = (α.app X).hom v := rfl

@[simp]
theorem quotientNatIsoOfSurjective_inv_apply (α : T.toFunctor ⟶ H)
    (hker : ∀ (X : C) (v : T.representation X),
      v ∈ S.lowerInUpper T X ↔ (α.app X).hom v = 0)
    (hsurj : ∀ X, Function.Surjective (α.app X).hom)
    (X : C) (v : T.representation X) :
    ((S.quotientNatIsoOfSurjective T α hker hsurj).inv.app X).hom
        ((α.app X).hom v) = (S.quotientProjection T X).hom v :=
  Rep.inv_hom_apply _ _ ((S.quotientNatIsoOfSurjective T α hker hsurj).app X)
    ((S.quotientProjection T X).hom v)

end Langlands.RepSubfunctor
