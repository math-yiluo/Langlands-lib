import Mathlib.CategoryTheory.Sites.Descent.IsPrestack
import Mathlib.CategoryTheory.Yoneda

/-! # Actual point fibres of a category-valued pseudofunctor -/

universe v v' u u'

open CategoryTheory CategoryTheory.Bicategory Opposite

noncomputable section

namespace Langlands.CategoryTheory.PseudofunctorPointFiber

variable {C : Type u} [Category.{v} C]
  {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}

open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

/-- Pull back an actual isomorphism, using the composition comparisons. -/
def pullIso {X₁ X₂ : C} {M₁ : F.obj (.mk (op X₁))}
    {M₂ : F.obj (.mk (op X₂))} {Y : C}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (e : (F.map f₁.op.toLoc).toFunctor.obj M₁ ≅
      (F.map f₂.op.toLoc).toFunctor.obj M₂)
    {Y' : C} (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch)
    (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    (F.map gf₁.op.toLoc).toFunctor.obj M₁ ≅
      (F.map gf₂.op.toLoc).toFunctor.obj M₂ :=
  (Cat.Hom.toNatIso (F.mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
    (by aesop))).app M₁ ≪≫
    (F.map g.op.toLoc).toFunctor.mapIso e ≪≫
      ((Cat.Hom.toNatIso (F.mapComp' f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (by aesop))).app M₂).symm

@[simp]
lemma pullIso_hom {X₁ X₂ : C} {M₁ : F.obj (.mk (op X₁))}
    {M₂ : F.obj (.mk (op X₂))} {Y : C}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (e : (F.map f₁.op.toLoc).toFunctor.obj M₁ ≅
      (F.map f₂.op.toLoc).toFunctor.obj M₂)
    {Y' : C} (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    (pullIso e g gf₁ gf₂ hgf₁ hgf₂).hom = pullHom e.hom g gf₁ gf₂ hgf₁ hgf₂ := rfl

@[simp]
lemma pullIso_id {X₁ X₂ : C} {M₁ : F.obj (.mk (op X₁))}
    {M₂ : F.obj (.mk (op X₂))} {Y : C}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (e : (F.map f₁.op.toLoc).toFunctor.obj M₁ ≅
      (F.map f₂.op.toLoc).toFunctor.obj M₂) :
    pullIso e (𝟙 Y) f₁ f₂ = e := by
  apply Iso.ext
  exact pullHom_id e.hom

@[simp]
lemma pullIso_pullIso {X₁ X₂ : C} {M₁ : F.obj (.mk (op X₁))}
    {M₂ : F.obj (.mk (op X₂))} {Y : C}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (e : (F.map f₁.op.toLoc).toFunctor.obj M₁ ≅
      (F.map f₂.op.toLoc).toFunctor.obj M₂)
    {Y' : C} (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    {Y'' : C} (g' : Y'' ⟶ Y') (g'f₁ : Y'' ⟶ X₁) (g'f₂ : Y'' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch)
    (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch)
    (hg'f₁ : g' ≫ gf₁ = g'f₁ := by cat_disch)
    (hg'f₂ : g' ≫ gf₂ = g'f₂ := by cat_disch) :
    pullIso (pullIso e g gf₁ gf₂ hgf₁ hgf₂) g' g'f₁ g'f₂ hg'f₁ hg'f₂ =
      pullIso e (g' ≫ g) g'f₁ g'f₂ := by
  apply Iso.ext
  exact pullHom_pullHom e.hom g gf₁ gf₂ g' g'f₁ g'f₂ hgf₁ hgf₂ hg'f₁ hg'f₂

variable (F) {U T : C} (ξ : F.obj (.mk (op U))) (η : F.obj (.mk (op T)))

/-- A point of the fibre has a genuine base map and a genuine isomorphism. -/
abbrev Points (Z : Over T) : Type (max v v') :=
  Σ a : Z.left ⟶ U,
    (F.map a.op.toLoc).toFunctor.obj ξ ≅
      (F.map Z.hom.op.toLoc).toFunctor.obj η

/-- Restrict both the base map and the isomorphism along a slice morphism. -/
def restrict {Z Z' : Over T} (q : Z' ⟶ Z) :
    Points F ξ η Z → Points F ξ η Z' :=
  fun x ↦ ⟨q.left ≫ x.1, pullIso x.2 q.left (q.left ≫ x.1) Z'.hom rfl q.w⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma restrict_id (Z : Over T) (x : Points F ξ η Z) :
    restrict F ξ η (𝟙 Z) x = x := by
  rcases x with ⟨a, e⟩
  dsimp only [restrict, Over.id_left]
  have h (b : Z.left ⟶ U) (hb : (𝟙 Z.left) ≫ a = b) :
      (⟨b, pullIso e (𝟙 Z.left) b Z.hom hb (by simp)⟩ : Points F ξ η Z) =
        ⟨a, e⟩ := by
    have hba : b = a := hb.symm.trans (Category.id_comp a)
    cases hba.symm
    refine Sigma.ext ?_ ?_
    · rfl
    · exact heq_of_eq (pullIso_id e)
  exact h _ rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma restrict_comp {Z Z' Z'' : Over T} (q : Z' ⟶ Z) (q' : Z'' ⟶ Z')
    (x : Points F ξ η Z) :
    restrict F ξ η (q' ≫ q) x = restrict F ξ η q' (restrict F ξ η q x) := by
  rcases x with ⟨a, e⟩
  simp only [restrict, Over.comp_left, pullIso_pullIso]
  have hw : (q'.left ≫ q.left) ≫ Z.hom = Z''.hom := by
    rw [Category.assoc, q.w, q'.w]
  have h (b : Z''.left ⟶ U) (hb : (q'.left ≫ q.left) ≫ a = b) :
      (⟨(q'.left ≫ q.left) ≫ a,
        pullIso e (q'.left ≫ q.left) ((q'.left ≫ q.left) ≫ a) Z''.hom rfl hw⟩ :
        Points F ξ η Z'') =
      ⟨b, pullIso e (q'.left ≫ q.left) b Z''.hom hb hw⟩ := by
    subst b
    rfl
  exact h _ (Category.assoc _ _ _)

/-- The actual point-fibre presheaf, before any representability assertion. -/
def presheaf : (Over T)ᵒᵖ ⥤ Type (max v v') where
  obj Z := Points F ξ η Z.unop
  map q := ↾(restrict F ξ η q.unop)
  map_id Z := by
    apply ConcreteCategory.hom_ext
    intro x
    exact restrict_id F ξ η Z.unop x
  map_comp q q' := by
    apply ConcreteCategory.hom_ext
    intro x
    exact restrict_comp F ξ η q.unop q'.unop x

/-- Forget the isomorphism and retain the actual map into `U`. -/
def projection :
    presheaf F ξ η ⟶ (Over.forget T).op ⋙ (uliftYoneda.{v'}).obj U where
  app _ := ↾fun x ↦ ULift.up x.1
  naturality {_ _} _ := rfl

end Langlands.CategoryTheory.PseudofunctorPointFiber
