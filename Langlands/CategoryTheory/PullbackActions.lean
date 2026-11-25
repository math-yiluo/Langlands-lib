import Mathlib.CategoryTheory.Action.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Actions induced by an arbitrary categorical pullback -/

noncomputable section

universe u v z

namespace Langlands.CategoricalPullback

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {G : Type z} [Group G]
variable {P U V B : C} {p : P ⟶ U} {q : P ⟶ V} {f : U ⟶ B} {g : V ⟶ B}

/-- The endomorphism of a pullback induced by compatible automorphisms of its
cospan. No chosen pullback object or pointwise description is used. -/
def pullbackActionEnd (h : IsPullback p q f g)
    (σU : G →* Aut U) (σV : G →* Aut V) (σB : G →* Aut B)
    (hf : ∀ a, (σU a).asIso.hom ≫ f = f ≫ (σB a).asIso.hom)
    (hg : ∀ a, (σV a).asIso.hom ≫ g = g ≫ (σB a).asIso.hom) (a : G) : P ⟶ P :=
  h.lift (p ≫ (σU a).asIso.hom) (q ≫ (σV a).asIso.hom) (by
    calc
      (p ≫ (σU a).asIso.hom) ≫ f = (p ≫ f) ≫ (σB a).asIso.hom := by
        rw [Category.assoc, hf, ← Category.assoc]
      _ = (q ≫ g) ≫ (σB a).asIso.hom := by rw [h.w]
      _ = (q ≫ (σV a).asIso.hom) ≫ g := by simp only [Category.assoc, hg])

@[reassoc (attr := simp)]
theorem pullbackActionEnd_fst (h : IsPullback p q f g)
    (σU : G →* Aut U) (σV : G →* Aut V) (σB : G →* Aut B)
    (hf : ∀ a, (σU a).asIso.hom ≫ f = f ≫ (σB a).asIso.hom)
    (hg : ∀ a, (σV a).asIso.hom ≫ g = g ≫ (σB a).asIso.hom) (a : G) :
    pullbackActionEnd h σU σV σB hf hg a ≫ p = p ≫ (σU a).asIso.hom :=
  h.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pullbackActionEnd_snd (h : IsPullback p q f g)
    (σU : G →* Aut U) (σV : G →* Aut V) (σB : G →* Aut B)
    (hf : ∀ a, (σU a).asIso.hom ≫ f = f ≫ (σB a).asIso.hom)
    (hg : ∀ a, (σV a).asIso.hom ≫ g = g ≫ (σB a).asIso.hom) (a : G) :
    pullbackActionEnd h σU σV σB hf hg a ≫ q = q ≫ (σV a).asIso.hom :=
  h.lift_snd _ _ _

/-- The action on a supplied categorical pullback, obtained by its universal
property from the three compatible cospan actions. -/
def pullbackAction (h : IsPullback p q f g)
    (σU : G →* Aut U) (σV : G →* Aut V) (σB : G →* Aut B)
    (hf : ∀ a, (σU a).asIso.hom ≫ f = f ≫ (σB a).asIso.hom)
    (hg : ∀ a, (σV a).asIso.hom ≫ g = g ≫ (σB a).asIso.hom) : G →* Aut P :=
  Action.ρAut (V := C) {
    V := P
    ρ := {
      toFun := fun a ↦ End.of (pullbackActionEnd h σU σV σB hf hg a)
      map_one' := by
        apply End.ext
        apply h.hom_ext <;> simp [show (1 : Aut U).asIso.hom = 𝟙 U from rfl,
          show (1 : Aut V).asIso.hom = 𝟙 V from rfl]
      map_mul' := by
        intro a b
        apply End.ext
        change pullbackActionEnd h σU σV σB hf hg (a * b) =
          pullbackActionEnd h σU σV σB hf hg b ≫
            pullbackActionEnd h σU σV σB hf hg a
        apply h.hom_ext <;> simp [map_mul, Aut.Aut_mul_def, Iso.trans, Category.assoc]
    }
  }

@[reassoc (attr := simp)]
theorem pullbackAction_fst (h : IsPullback p q f g)
    (σU : G →* Aut U) (σV : G →* Aut V) (σB : G →* Aut B)
    (hf : ∀ a, (σU a).asIso.hom ≫ f = f ≫ (σB a).asIso.hom)
    (hg : ∀ a, (σV a).asIso.hom ≫ g = g ≫ (σB a).asIso.hom) (a : G) :
    (pullbackAction h σU σV σB hf hg a).asIso.hom ≫ p = p ≫ (σU a).asIso.hom :=
  pullbackActionEnd_fst h σU σV σB hf hg a

@[reassoc (attr := simp)]
theorem pullbackAction_snd (h : IsPullback p q f g)
    (σU : G →* Aut U) (σV : G →* Aut V) (σB : G →* Aut B)
    (hf : ∀ a, (σU a).asIso.hom ≫ f = f ≫ (σB a).asIso.hom)
    (hg : ∀ a, (σV a).asIso.hom ≫ g = g ≫ (σB a).asIso.hom) (a : G) :
    (pullbackAction h σU σV σB hf hg a).asIso.hom ≫ q = q ≫ (σV a).asIso.hom :=
  pullbackActionEnd_snd h σU σV σB hf hg a

end Langlands.CategoricalPullback
