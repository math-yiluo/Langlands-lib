import Langlands.AlgebraicGeometry.Picard.AtlasArrowPresheaf
import Langlands.AlgebraicGeometry.Picard.ParallelIsomorphismSchemes
import Langlands.CategoryTheory.OverTotalPresheaf
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-! # The full endpoint pullback of actual Picard arrows -/

universe v v' u u'

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Functor
  CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.CategoryTheory.PseudofunctorPointFiber

variable {C : Type u} [Category.{v} C]
  {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} {U : C} {ξ : F.obj (.mk (op U))}

/-- Equal endpoint maps give equal full pulled-back arrow data. -/
lemma totalPullIso_congr {V W : C} {a b : V ⟶ U}
    (e : (F.map a.op.toLoc).toFunctor.obj ξ ≅ (F.map b.op.toLoc).toFunctor.obj ξ)
    (g : W ⟶ V) (a₁ a₂ b₁ b₂ : W ⟶ U) (ha : a₁ = a₂) (hb : b₁ = b₂)
    (ha₁ : g ≫ a = a₁) (ha₂ : g ≫ a = a₂) (hb₁ : g ≫ b = b₁) (hb₂ : g ≫ b = b₂) :
    (⟨b₁, a₁, pullIso e g a₁ b₁ ha₁ hb₁⟩ : (presheaf F ξ ξ).OverTotal W) =
      ⟨b₂, a₂, pullIso e g a₂ b₂ ha₂ hb₂⟩ := by
  subst a₂
  subst b₂
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Retain both fixed endpoint composites of an actual parallel isomorphism. -/
def totalParallelArrowMap (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})
    {U T : C} (ξ : F.obj (.mk (op U))) (a b : T ⟶ U) :
    (parallelIsoPresheaf F ξ a b).overTotal ⟶ (presheaf F ξ ξ).overTotal where
  app _ := ↾fun x ↦ ⟨x.1 ≫ b, x.1 ≫ a, x.2⟩
  naturality {V W} g := by
    apply ConcreteCategory.hom_ext
    intro x
    change (⟨(g.unop ≫ x.1) ≫ b, (g.unop ≫ x.1) ≫ a,
        pullIso x.2 g.unop ((g.unop ≫ x.1) ≫ a) ((g.unop ≫ x.1) ≫ b)
          (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm⟩ :
            (presheaf F ξ ξ).OverTotal W.unop) =
      ⟨g.unop ≫ (x.1 ≫ b), g.unop ≫ (x.1 ≫ a),
        pullIso x.2 g.unop (g.unop ≫ (x.1 ≫ a)) (g.unop ≫ (x.1 ≫ b)) rfl rfl⟩
    exact totalPullIso_congr x.2 g.unop _ _ _ _
      (Category.assoc _ _ _) (Category.assoc _ _ _) _ _ _ _

end Langlands.CategoryTheory.PseudofunctorPointFiber

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

open Langlands.CategoryTheory.PseudofunctorPointFiber

variable {S X : Scheme.{u}} (f : X ⟶ S) {U T : Over S}
  (L : LineBundle ((relativeSpace f).obj U)) (a b : T ⟶ U)

/-- The pair of actual family endpoint maps on all tests. -/
def atlasEndpointPresheaf (U : Over S) : AlgebraicSpace.Presheaf S where
  obj V := ULift.{u + 1} ((V.unop ⟶ U) × (V.unop ⟶ U))
  map g := ↾fun x ↦ ULift.up (g.unop ≫ x.down.1, g.unop ≫ x.down.2)
  map_id V := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg ULift.up (Prod.ext (Category.id_comp _) (Category.id_comp _))
  map_comp g h := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg ULift.up (Prod.ext (Category.assoc _ _ _) (Category.assoc _ _ _))

/-- The complete endpoint map of an actual Picard arrow. -/
def atlasArrowEndpoint : atlasArrowPresheaf f L ⟶ atlasEndpointPresheaf U where
  app _ := ↾fun x ↦ ULift.up (x.down.2.1, x.down.1)
  naturality {_ _} _ := rfl

/-- The endpoint pair determined by two fixed maps of actual schemes. -/
def familyEndpointMap :
    (AlgebraicSpace.schemeYoneda S).obj T ⟶ atlasEndpointPresheaf U where
  app _ := ↾fun q ↦ ULift.up (q.down ≫ a, q.down ≫ b)
  naturality {_ _} g := by
    apply ConcreteCategory.hom_ext
    intro q
    exact congrArg ULift.up (Prod.ext (Category.assoc _ _ _) (Category.assoc _ _ _))

/-- The full presheaf of a base map and a parallel actual isomorphism. -/
def totalParallelIsomorphismPresheaf : AlgebraicSpace.Presheaf S :=
  (parallelIsoPresheaf (relative f) (Core.mk L) a b).overTotal ⋙ uliftFunctor.{u + 1}

/-- Forget the common base map and retain the actual arrow. -/
def totalParallelIsomorphismArrowMap :
    totalParallelIsomorphismPresheaf f L a b ⟶ atlasArrowPresheaf f L :=
  Functor.whiskerRight (totalParallelArrowMap (relative f) (Core.mk L) a b)
    uliftFunctor.{u + 1}

/-- Retain the actual common base map of a parallel isomorphism. -/
def totalParallelIsomorphismBaseMap :
    totalParallelIsomorphismPresheaf f L a b ⟶ (AlgebraicSpace.schemeYoneda S).obj T where
  app _ := ↾fun x ↦ ULift.up x.down.1
  naturality {_ _} _ := rfl

/-- The complete presheaf of parallel arrows is the endpoint base change. -/
lemma totalParallelIsomorphism_isPullback :
    IsPullback (totalParallelIsomorphismArrowMap f L a b)
      (totalParallelIsomorphismBaseMap f L a b) (atlasArrowEndpoint f L)
      (familyEndpointMap a b) := by
  apply IsPullback.of_forall_isPullback_app
  intro V
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro x
    rfl
  · rintro ⟨⟨q, δ⟩⟩ ⟨⟨q', δ'⟩⟩ ⟨hδ, hq⟩
    have hq' : q = q' := congrArg ULift.down hq
    subst q'
    have h₀ := congrArg ULift.down hδ
    have h₁ := eq_of_heq (Sigma.mk.inj h₀).2
    have h₂ := eq_of_heq (Sigma.mk.inj h₁).2
    change δ = δ' at h₂
    subst δ'
    rfl
  · rintro ⟨⟨b', a', δ⟩⟩ ⟨q⟩ h
    have hp : (a', b') = (q ≫ a, q ≫ b) := congrArg ULift.down h
    have ha := congrArg Prod.fst hp
    have hb := congrArg Prod.snd hp
    change a' = q ≫ a at ha
    change b' = q ≫ b at hb
    subst a'
    subst b'
    exact ⟨ULift.up ⟨q, δ⟩, rfl, rfl⟩

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
