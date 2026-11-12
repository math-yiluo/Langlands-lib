import Langlands.CategoryTheory.Sites.PseudofunctorPointFiberAtlasRestriction
import Langlands.CategoryTheory.Sites.StackPullback
import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Point fibres of a pseudofunctor reindexed along a left adjoint -/

universe v v' u₁ u₂ u'

open CategoryTheory CategoryTheory.Bicategory Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.CategoryTheory.PseudofunctorPointFiberReindex

open Langlands.CategoryTheory.PseudofunctorPointFiber
open Langlands.CategoryTheory.StackPullback
open Langlands.CategoryTheory.PseudofunctorPointFiberAtlasRestriction (atlasComparison)

variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]
  (Φ : C ⥤ D) (P : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{v', u'})

/-- Coherent pullback of isomorphisms for the reindexed pseudofunctor is coherent
pullback along the image arrows. -/
lemma pullIso_reindex {X₁ X₂ Y Y' : C}
    {M₁ : P.obj (.mk (op (Φ.obj X₁)))} {M₂ : P.obj (.mk (op (Φ.obj X₂)))}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (e : (P.map (Φ.map f₁).op.toLoc).toFunctor.obj M₁ ≅
      (P.map (Φ.map f₂).op.toLoc).toFunctor.obj M₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) :
    pullIso (F := reindex Φ P) e g gf₁ gf₂ h₁ h₂ =
      pullIso (F := P) e (Φ.map g) (Φ.map gf₁) (Φ.map gf₂)
        (by rw [← Φ.map_comp, h₁]) (by rw [← Φ.map_comp, h₂]) := by
  apply Iso.ext
  exact pullHom_reindex Φ P e.hom g gf₁ gf₂ h₁ h₂

section

variable {U T : C} (ξ : P.obj (.mk (op (Φ.obj U))))
  (η : P.obj (.mk (op (Φ.obj T))))

/-- Apply `Φ` to the actual base map; the actual isomorphism is unchanged. -/
def mapPoints (Z : Over T) :
    Points (reindex Φ P) ξ η Z → Points P ξ η ((Over.post Φ).obj Z) :=
  fun x ↦ ⟨Φ.map x.1, x.2⟩

/-- Applying `Φ` commutes with restriction along every slice morphism. -/
lemma mapPoints_restrict {Z Z' : Over T} (q : Z' ⟶ Z)
    (x : Points (reindex Φ P) ξ η Z) :
    mapPoints Φ P ξ η Z' (restrict (reindex Φ P) ξ η q x) =
      restrict P ξ η ((Over.post Φ).map q) (mapPoints Φ P ξ η Z x) := by
  rcases x with ⟨a, e⟩
  dsimp only [mapPoints, restrict]
  rw [pullIso_reindex]
  have h (b : Φ.obj Z'.left ⟶ Φ.obj U) (hb : Φ.map (q.left ≫ a) = b) :
      (⟨Φ.map (q.left ≫ a),
        pullIso (F := P) e (Φ.map q.left) (Φ.map (q.left ≫ a)) (Φ.map Z'.hom)
          ((Φ.map_comp _ _).symm.trans rfl)
          ((Φ.map_comp _ _).symm.trans (congrArg Φ.map q.w))⟩ :
        Points P ξ η ((Over.post Φ).obj Z')) =
      ⟨b, pullIso (F := P) e (Φ.map q.left) b (Φ.map Z'.hom)
          ((Φ.map_comp _ _).symm.trans hb)
          ((Φ.map_comp _ _).symm.trans (congrArg Φ.map q.w))⟩ := by
    subst b
    rfl
  exact h _ (Φ.map_comp _ _)

/-- Applying `Φ` to base maps is a natural transformation of point fibres. -/
def presheafMap :
    presheaf (reindex Φ P) ξ η ⟶ (Over.post Φ).op ⋙ presheaf P ξ η where
  app Z := ↾(mapPoints Φ P ξ η Z.unop)
  naturality {_ _} q := by
    apply ConcreteCategory.hom_ext
    intro x
    exact mapPoints_restrict Φ P ξ η q.unop x

end

section adjunction

variable {Φ} {Ψ : D ⥤ C} (adj : Φ ⊣ Ψ) {V : D} (ζ : P.obj (.mk (op V)))
  {T : C} (η : P.obj (.mk (op (Φ.obj T))))

/-- The object over `Ψ V` obtained by pulling back `ζ` along the counit. -/
abbrev counitObj : (reindex Φ P).obj (.mk (op (Ψ.obj V))) :=
  (P.map (adj.counit.app V).op.toLoc).toFunctor.obj ζ

/-- A point over `Ψ V` gives the point over `V` whose base map is the adjoint
transpose, with the composition comparison along the counit. -/
def adjPoints (Z : Over T) :
    Points (reindex Φ P) (counitObj P adj ζ) η Z →
      Points P ζ η ((Over.post Φ).obj Z) :=
  fun x ↦ PseudofunctorPointFiberAtlasRestriction.mapPoints P (adj.counit.app V) ζ η _
    (mapPoints Φ P _ η Z x)

lemma adjPoints_fst (Z : Over T) (x : Points (reindex Φ P) (counitObj P adj ζ) η Z) :
    (adjPoints P adj ζ η Z x).1 = (adj.homEquiv _ _).symm x.1 := by
  rw [Adjunction.homEquiv_counit]
  rfl

lemma adjPoints_injective (Z : Over T) : Function.Injective (adjPoints P adj ζ η Z) := by
  rintro ⟨a, e⟩ ⟨b, e'⟩ h
  have hab : a = b := by
    have := congrArg Sigma.fst h
    rw [adjPoints_fst, adjPoints_fst] at this
    exact (adj.homEquiv _ _).symm.injective this
  subst b
  have he : atlasComparison P (adj.counit.app V) ζ (Φ.map a) ≪≫ e =
      atlasComparison P (adj.counit.app V) ζ (Φ.map a) ≪≫ e' := by
    simpa only [adjPoints, PseudofunctorPointFiberAtlasRestriction.mapPoints, mapPoints,
      Sigma.mk.injEq, heq_eq_eq, true_and] using h
  have he' : e = e' := by
    apply Iso.ext
    exact (cancel_epi (atlasComparison P (adj.counit.app V) ζ (Φ.map a)).hom).mp
      (congrArg Iso.hom he)
  subst e'
  rfl

lemma adjPoints_surjective (Z : Over T) : Function.Surjective (adjPoints P adj ζ η Z) := by
  rintro ⟨b, e⟩
  obtain ⟨a, ha⟩ : ∃ a : Z.left ⟶ Ψ.obj V, Φ.map a ≫ adj.counit.app V = b :=
    ⟨adj.homEquiv Z.left V b, by simp [Adjunction.homEquiv_unit]⟩
  subst ha
  refine ⟨⟨a, (atlasComparison P (adj.counit.app V) ζ (Φ.map a)).symm ≪≫ e⟩, ?_⟩
  simp [adjPoints, PseudofunctorPointFiberAtlasRestriction.mapPoints, mapPoints]

/-- Adjoint transposition gives equivalences of actual point types. -/
def adjPointsEquiv (Z : Over T) :
    Points (reindex Φ P) (counitObj P adj ζ) η Z ≃ Points P ζ η ((Over.post Φ).obj Z) :=
  Equiv.ofBijective (adjPoints P adj ζ η Z)
    ⟨adjPoints_injective P adj ζ η Z, adjPoints_surjective P adj ζ η Z⟩

lemma adjPoints_restrict {Z Z' : Over T} (q : Z' ⟶ Z)
    (x : Points (reindex Φ P) (counitObj P adj ζ) η Z) :
    adjPoints P adj ζ η Z' (restrict (reindex Φ P) _ η q x) =
      restrict P ζ η ((Over.post Φ).map q) (adjPoints P adj ζ η Z x) := by
  dsimp only [adjPoints]
  rw [mapPoints_restrict, PseudofunctorPointFiberAtlasRestriction.mapPoints_restrict]

/-- The point fibre of the reindexed pseudofunctor at the counit pullback is the
point fibre of the original pseudofunctor, restricted along `Over.post Φ`. -/
def adjPresheafIso :
    presheaf (reindex Φ P) (counitObj P adj ζ) η ≅ (Over.post Φ).op ⋙ presheaf P ζ η :=
  NatIso.ofComponents (fun Z ↦ (adjPointsEquiv P adj ζ η Z.unop).toIso) (by
    intro Z Z' q
    apply ConcreteCategory.hom_ext
    intro x
    exact adjPoints_restrict P adj ζ η q.unop x)

end adjunction

end Langlands.CategoryTheory.PseudofunctorPointFiberReindex
