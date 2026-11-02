import Langlands.AlgebraicGeometry.AlgebraicSpace.MonomorphismLocallyFiniteTypeSchemeStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotientStatement

/-! # Schemeness of an algebraic space with an injective pair of maps to a scheme

Consequences of `MonomorphismLocallyFiniteTypeSchemeStatement` for a pair of maps
`s t : R ⟶ U` that is injective on all scheme points, and for the arrow space of a smooth
relation as in `SmoothRelationQuotientStatement`.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace MonomorphismPairScheme

variable {S : Scheme.{u}} {F : Presheaf S} {U : Over S}

/-- The pair `(s, t)` as a map to the functor of points of the product `U ⨯ U` in `Over S`. -/
def pairMap (s t : F ⟶ (schemeYoneda S).obj U) : F ⟶ (schemeYoneda S).obj (U ⨯ U) where
  app T := ↾(fun r ↦ ULift.up (prod.lift (s.app T r).down (t.app T r).down))
  naturality T T' g := by
    ext r
    apply ULift.ext
    apply prod.hom_ext <;> simp

@[simp]
lemma pairMap_app_down (s t : F ⟶ (schemeYoneda S).obj U) (T : (Over S)ᵒᵖ) (r : F.obj T) :
    ((pairMap s t).app T r).down = prod.lift (s.app T r).down (t.app T r).down := rfl

/-- The pair map is a monomorphism when the pair is injective on every scheme point. -/
lemma mono_pairMap (s t : F ⟶ (schemeYoneda S).obj U)
    (inj : ∀ T : Over S,
      Function.Injective (fun r : F.obj (op T) ↦ (s.app (op T) r, t.app (op T) r))) :
    Mono (pairMap s t) := by
  rw [NatTrans.mono_iff_mono_app]
  intro T
  rw [mono_iff_injective]
  intro r r' h
  have h' := congrArg ULift.down h
  simp only [pairMap_app_down] at h'
  apply inj T.unop
  have h1 := congrArg (· ≫ prod.fst) h'
  have h2 := congrArg (· ≫ prod.snd) h'
  simp only [prod.lift_fst, prod.lift_snd] at h1 h2
  exact Prod.ext (ULift.ext _ _ h1) (ULift.ext _ _ h2)

/-- On a scheme, the pair map is induced by the pair of scheme morphisms. -/
lemma comp_pairMap (s t : F ⟶ (schemeYoneda S).obj U) {W : Over S}
    (b : (schemeYoneda S).obj W ⟶ F) (s₀ t₀ : W ⟶ U)
    (hs : b ≫ s = (schemeYoneda S).map s₀) (ht : b ≫ t = (schemeYoneda S).map t₀) :
    b ≫ pairMap s t = (schemeYoneda S).map (prod.lift s₀ t₀) := by
  ext T x
  apply ULift.ext
  have hs' := congrArg ULift.down (ConcreteCategory.congr_hom (NatTrans.congr_app hs T) x)
  have ht' := congrArg ULift.down (ConcreteCategory.congr_hom (NatTrans.congr_app ht T) x)
  dsimp at hs' ht' ⊢
  apply prod.hom_ext <;> simp [hs', ht']

/-- An algebraic space with a pair of maps to `U`, injective on every scheme point, is
represented by a scheme if on some surjective etale atlas the first map is induced by a
morphism locally of finite type. -/
theorem isRepresentedByScheme_of_injective_pair
    (hP1 : MonomorphismLocallyFiniteTypeSchemeStatement.{u})
    (R : AlgebraicSpace S) (s t : R.presheaf ⟶ (schemeYoneda S).obj U)
    (inj : ∀ T : Over S,
      Function.Injective (fun r : R.sections T ↦ (s.app (op T) r, t.app (op T) r)))
    {W : Over S} (b : (schemeYoneda S).obj W ⟶ R.presheaf) (s₀ t₀ : W ⟶ U)
    (hb : IsEtale b) (hbs : IsSurjective b)
    (hs : b ≫ s = (schemeYoneda S).map s₀) (ht : b ≫ t = (schemeYoneda S).map t₀)
    (hlft : LocallyOfFiniteType s₀.left) :
    IsRepresentedByScheme R := by
  refine hP1 S R (U ⨯ U) (pairMap s t) (mono_pairMap s t inj)
    ⟨W, b, prod.lift s₀ t₀, hb, hbs, comp_pairMap s t b s₀ t₀ hs ht, ?_⟩
  have : LocallyOfFiniteType ((prod.lift s₀ t₀).left ≫ (prod.fst : U ⨯ U ⟶ U).left) := by
    rw [← Over.comp_left, prod.lift_fst]
    exact hlft
  exact locallyOfFiniteType_of_comp _ (prod.fst : U ⨯ U ⟶ U).left

open SmoothRelationQuotient in
/-- The arrow space of a smooth equivalence relation, in the sense of
`SmoothRelationQuotientStatement`, is represented by a scheme. -/
theorem isRepresentedByScheme_of_hasSmoothProjections
    (hP1 : MonomorphismLocallyFiniteTypeSchemeStatement.{u})
    (R : AlgebraicSpace S) (s t : R.presheaf ⟶ (schemeYoneda S).obj U)
    (h : IsEquivalenceRelation R s t) (hsm : HasSmoothProjections R s t) :
    IsRepresentedByScheme R := by
  obtain ⟨W, b, s₀, t₀, hb, hbs, hs, ht, hs₀, -⟩ := hsm
  exact isRepresentedByScheme_of_injective_pair hP1 R s t (fun T ↦ (h T).1) b s₀ t₀ hb hbs
    hs ht inferInstance

end MonomorphismPairScheme

end Langlands.AlgebraicGeometry.AlgebraicSpace
