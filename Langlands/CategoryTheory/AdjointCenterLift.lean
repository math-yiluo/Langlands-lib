import Mathlib.CategoryTheory.Center.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Lifting central components through a faithful left adjoint

Let `I : C ⥤ D` be a faithful functor with a right adjoint `R`, `C` abelian, and `z` an element
of the centre of `D`. If every nonzero morphism out of an object `X` of `C` is detected by a
morphism from an object on which the component of `z` lifts through `I`, then the component
`z.app (I.obj X)` lifts through `I`.
-/

noncomputable section

universe vC vD uC uD

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Abelian C]
  {I : C ⥤ D} {R : D ⥤ C}

/-- **Lifting a central component through a faithful left adjoint.** Let `adj : I ⊣ R` with `I`
faithful and `C` abelian, `z` central in `D` and `X : C`. Suppose that for every nonzero
`φ : X ⟶ Y` there are an object `Q` and `s : Q ⟶ X` with `s ≫ φ ≠ 0` such that
`z.app (I.obj Q)` is `I.map f` for some `f : Q ⟶ Q`. Then `z.app (I.obj X)` is `I.map y` for
some `y : X ⟶ X`. -/
theorem exists_map_eq_center_app_of_detecting [I.Faithful] (adj : I ⊣ R) (z : CatCenter D)
    (X : C)
    (hdet : ∀ (Y : C) (φ : X ⟶ Y), φ ≠ 0 →
      ∃ (Q : C) (s : Q ⟶ X), s ≫ φ ≠ 0 ∧ ∃ f : Q ⟶ Q, I.map f = z.app (I.obj Q)) :
    ∃ y : X ⟶ X, I.map y = z.app (I.obj X) := by
  let η : X ⟶ R.obj (I.obj X) := adj.unit.app X
  let zh : X ⟶ R.obj (I.obj X) := adj.homEquiv _ _ (z.app (I.obj X))
  -- On a liftable object `Q`, the adjunct of `z` composed with `s` factors through the unit.
  have key : ∀ (Q : C) (s : Q ⟶ X) (f : Q ⟶ Q), I.map f = z.app (I.obj Q) →
      s ≫ zh = (f ≫ s) ≫ η := by
    intro Q s f hf
    have h1 : s ≫ zh = adj.homEquiv _ _ (I.map s ≫ z.app (I.obj X)) := by
      simp only [zh, Adjunction.homEquiv_unit, Functor.map_comp]
      rw [← Category.assoc (adj.unit.app Q), adj.unit_naturality s, Category.assoc]
    have h2 : (f ≫ s) ≫ η = adj.homEquiv _ _ (I.map (f ≫ s)) := by
      simp only [η, Adjunction.homEquiv_unit]
      exact (adj.unit_naturality (f ≫ s)).symm
    rw [h1, h2, CatCenter.naturality z (I.map s), Functor.map_comp, hf]
  have hzero : zh ≫ cokernel.π η = 0 := by
    by_contra hne
    obtain ⟨Q, s, hs, f, hf⟩ := hdet _ _ hne
    apply hs
    rw [← Category.assoc, key Q s f hf, Category.assoc, cokernel.condition, comp_zero]
  refine ⟨Abelian.monoLift η zh hzero, ?_⟩
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, adj.unit_naturality]
  exact Abelian.monoLift_comp η zh hzero

end Langlands.Renard
