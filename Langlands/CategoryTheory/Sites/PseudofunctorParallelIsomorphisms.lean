import Langlands.CategoryTheory.Sites.PseudofunctorAutomorphismIso

/-! # Parallel isomorphisms and automorphisms on a complete slice -/

universe v v' u u'

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Functor Opposite

noncomputable section

namespace Langlands.CategoryTheory.PseudofunctorPointFiber

variable {C : Type u} [Category.{v} C]
  {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}

/-- Coherent pullback preserves composition of actual isomorphisms. -/
lemma pullIso_trans {X₁ X₂ X₃ : C} {M₁ : F.obj (.mk (op X₁))}
    {M₂ : F.obj (.mk (op X₂))} {M₃ : F.obj (.mk (op X₃))} {Y : C}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂} {f₃ : Y ⟶ X₃}
    (e₁ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ≅
      (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (e₂ : (F.map f₂.op.toLoc).toFunctor.obj M₂ ≅
      (F.map f₃.op.toLoc).toFunctor.obj M₃)
    {Y' : C} (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (gf₃ : Y' ⟶ X₃)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) (hgf₃ : g ≫ f₃ = gf₃) :
    pullIso (e₁ ≪≫ e₂) g gf₁ gf₃ hgf₁ hgf₃ =
      pullIso e₁ g gf₁ gf₂ hgf₁ hgf₂ ≪≫ pullIso e₂ g gf₂ gf₃ hgf₂ hgf₃ := by
  apply Iso.ext
  simp [pullIso]

/-- Change the restricting map by equality while retaining fixed endpoint maps. -/
lemma pullIso_congr {X₁ X₂ : C} {M₁ : F.obj (.mk (op X₁))}
    {M₂ : F.obj (.mk (op X₂))} {Y : C} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (e : (F.map f₁.op.toLoc).toFunctor.obj M₁ ≅ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    {Y' : C} (g g' : Y' ⟶ Y) (h : g = g') (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hg₁ : g ≫ f₁ = gf₁) (hg₂ : g ≫ f₂ = gf₂)
    (hg'₁ : g' ≫ f₁ = gf₁) (hg'₂ : g' ≫ f₂ = gf₂) :
    pullIso e g gf₁ gf₂ hg₁ hg₂ = pullIso e g' gf₁ gf₂ hg'₁ hg'₂ := by
  subst g'
  rfl

variable (F) {U T : C} (ξ : F.obj (.mk (op U))) (a b : T ⟶ U)

/-- Isomorphisms between the two actual pullbacks along fixed endpoint maps,
on every test over their common base. -/
def parallelIsoPresheaf : (Over T)ᵒᵖ ⥤ Type v' where
  obj Z := (F.map (Z.unop.hom ≫ a).op.toLoc).toFunctor.obj ξ ≅
    (F.map (Z.unop.hom ≫ b).op.toLoc).toFunctor.obj ξ
  map {Z W} p := ↾fun e ↦ pullIso e p.unop.left (W.unop.hom ≫ a) (W.unop.hom ≫ b)
    (p.unop.w_assoc a) (p.unop.w_assoc b)
  map_id Z := by
    apply ConcreteCategory.hom_ext
    intro e
    exact pullIso_id e
  map_comp {Z W V} p q := by
    apply ConcreteCategory.hom_ext
    intro e
    exact (pullIso_pullIso e p.unop.left (W.unop.hom ≫ a) (W.unop.hom ≫ b)
      q.unop.left (V.unop.hom ≫ a) (V.unop.hom ≫ b)
      (p.unop.w_assoc a) (p.unop.w_assoc b) (q.unop.w_assoc a) (q.unop.w_assoc b)).symm

variable (e : (F.map a.op.toLoc).toFunctor.obj ξ ≅ (F.map b.op.toLoc).toFunctor.obj ξ)

set_option backward.isDefEq.respectTransparency false in
/-- A fixed actual arrow identifies all parallel arrows with automorphisms
of its source, naturally on the entire test slice. -/
def automorphismParallelIso :
    (Over.map a).op ⋙ automorphismIsoPresheaf F ξ ≅ parallelIsoPresheaf F ξ a b :=
  NatIso.ofComponents (fun Z ↦ Equiv.toIso
    { toFun := fun α ↦ α ≪≫ pullIso e Z.unop.hom (Z.unop.hom ≫ a) (Z.unop.hom ≫ b) rfl rfl
      invFun := fun β ↦ β ≪≫
        (pullIso e Z.unop.hom (Z.unop.hom ≫ a) (Z.unop.hom ≫ b) rfl rfl).symm
      left_inv := fun α ↦ by simp [Iso.trans_assoc]
      right_inv := fun β ↦ by simp [Iso.trans_assoc] }) (by
    intro Z W p
    apply ConcreteCategory.hom_ext
    intro α
    change pullIso α p.unop.left (W.unop.hom ≫ a) (W.unop.hom ≫ a)
        (p.unop.w_assoc a) (p.unop.w_assoc a) ≪≫
      pullIso e W.unop.hom (W.unop.hom ≫ a) (W.unop.hom ≫ b) rfl rfl =
      pullIso (α ≪≫ pullIso e Z.unop.hom (Z.unop.hom ≫ a) (Z.unop.hom ≫ b) rfl rfl)
        p.unop.left (W.unop.hom ≫ a) (W.unop.hom ≫ b) (p.unop.w_assoc a) (p.unop.w_assoc b)
    rw [pullIso_trans _ _ _ _ (W.unop.hom ≫ a) _ _ (p.unop.w_assoc a)]
    rw [pullIso_pullIso e Z.unop.hom (Z.unop.hom ≫ a) (Z.unop.hom ≫ b)
      p.unop.left (W.unop.hom ≫ a) (W.unop.hom ≫ b)
      rfl rfl (p.unop.w_assoc a) (p.unop.w_assoc b)]
    have hδ := pullIso_congr e (p.unop.left ≫ Z.unop.hom) W.unop.hom p.unop.w
      (W.unop.hom ≫ a) (W.unop.hom ≫ b)
      (by rw [p.unop.w]) (by rw [p.unop.w]) rfl rfl
    exact congrArg
      (fun δ ↦ pullIso α p.unop.left (W.unop.hom ≫ a) (W.unop.hom ≫ a)
        (p.unop.w_assoc a) (p.unop.w_assoc a) ≪≫ δ) hδ.symm)

end Langlands.CategoryTheory.PseudofunctorPointFiber
