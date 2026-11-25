/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# The Hom formula for the mate of a transition between right adjoints

Source: Zheng, Construction 4.1, p. 21, the adjunction formula for truncation maps.
(blueprint: lem-pur-evaluation-transition-mate).
-/

@[expose] public section
set_option autoImplicit false
universe uA vA uB vB uS vS
namespace CategoryTheory.Adjunction
open CategoryTheory CategoryTheory.Category
variable {A : Type uA} {B : Type uB} {S : Type uS}
  [Category.{vA} A] [Category.{vB} B] [Category.{vS} S]
  {T : A ⥤ B} {R : B ⥤ A} {E₁ : B ⥤ S} {e₁ : S ⥤ B}
  {E₂ : A ⥤ S} {e₂ : S ⥤ A}

/-- The transition's conjugate under the composite scalar/evaluation adjunction.
Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-evaluation-transition-mate). -/
def compositeMate (a₁ : E₁ ⊣ e₁) (a₂ : E₂ ⊣ e₂) (b : T ⊣ R)
    (t : e₂ ⟶ e₁ ⋙ R) : T ⋙ E₁ ⟶ E₂ :=
  (conjugateEquiv a₂ (b.comp a₁)).symm t

/-- The mate of a right-adjoint transition has the required iterated Hom formula.
Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-evaluation-transition-mate).
Proof: take the conjugate of the transition under the adjunctions for `E₂` and
`T` followed by `E₁`. The unit equation for conjugation and naturality of the
transition identify its composite Hom transpose. Apply the scalar Hom equivalence
and its left-variable naturality to separate the two transposes. -/
theorem compositeMate_homEquiv (a₁ : E₁ ⊣ e₁) (a₂ : E₂ ⊣ e₂) (b : T ⊣ R)
    (t : e₂ ⟶ e₁ ⋙ R) :
    ∀ N M (f : E₂.obj N ⟶ M),
      a₁.homEquiv (T.obj N) M ((compositeMate a₁ a₂ b t).app N ≫ f) =
        T.map (a₂.homEquiv N M f) ≫ (b.homEquiv (e₂.obj M) (e₁.obj M)).symm (t.app M) := by
  let a := b.comp a₁
  let σ := (conjugateEquiv a₂ a).symm t
  intro N M f
  change a₁.homEquiv (T.obj N) M (σ.app N ≫ f) = _
  apply (b.homEquiv N (e₁.obj M)).injective
  rw [b.homEquiv_naturality_left, Equiv.apply_symm_apply]
  have hcomp : a.homEquiv N M (σ.app N ≫ f) =
      b.homEquiv N (e₁.obj M) (a₁.homEquiv (T.obj N) M (σ.app N ≫ f)) := by
    dsimp only [a]
    rw [comp_homEquiv]
    rfl
  rw [← hcomp]
  rw [a.homEquiv_unit, a₂.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    ← unit_conjugateEquiv_symm a₂ a t, Category.assoc, ← t.naturality]
  exact (Category.assoc _ _ _).symm

end CategoryTheory.Adjunction
