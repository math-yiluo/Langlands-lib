import Langlands.AbelianScheme.GroupScheme
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-! # Constructing categorical scheme actions from all-test laws -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {H : GroupScheme S} {X : Over S}

/-- An actual action morphism with identity and multiplication laws on every
scheme test supplies the standard categorical action structure. -/
@[instance_reducible]
def schemeActionOfPointLaws (hom : H.X ⊗ X ⟶ X)
    (hone : ∀ {T : Over S} (x : T ⟶ X),
      lift (1 : T ⟶ H.X) x ≫ hom = x)
    (hmul : ∀ {T : Over S} (h h' : T ⟶ H.X) (x : T ⟶ X),
      lift (h * h') x ≫ hom = lift h (lift h' x ≫ hom) ≫ hom) :
    ModObj H.X X where
  smul := hom
  one_smul := by
    change (η[H.X] ▷ X) ≫ hom = (λ_ X).hom
    have hp : lift (1 : 𝟙_ (Over S) ⊗ X ⟶ H.X) (snd _ _) = η[H.X] ▷ X := by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [lift_fst, whiskerRight_fst, Hom.one_def]
        exact congrArg (fun f => f ≫ η[H.X]) (toUnit_unique _ _)
      · simp only [lift_snd, whiskerRight_snd]
    rw [← hp, leftUnitor_hom]
    exact hone (snd _ _)
  mul_smul := by
    change (μ[H.X] ▷ X) ≫ hom =
      (α_ H.X H.X X).hom ≫ (H.X ◁ hom) ≫ hom
    let h := fst (H.X ⊗ H.X) X ≫ fst H.X H.X
    let h' := fst (H.X ⊗ H.X) X ≫ snd H.X H.X
    let x := snd (H.X ⊗ H.X) X
    have hp : lift h h' = fst (H.X ⊗ H.X) X := by
      dsimp [h, h']
      rw [← comp_lift, lift_fst_snd, Category.comp_id]
    have hl : lift (h * h') x = μ[H.X] ▷ X := by
      rw [Hom.mul_def, hp]
      dsimp [x]
      rw [← lift_whiskerRight, lift_fst_snd, Category.id_comp]
    have ha : lift h (lift h' x) = (α_ H.X H.X X).hom := by
      dsimp [h, h', x]
      apply CartesianMonoidalCategory.hom_ext
      · simp only [lift_fst, associator_hom_fst]
      · apply CartesianMonoidalCategory.hom_ext
        · simp only [Category.assoc, lift_snd_assoc, lift_fst, associator_hom_snd_fst]
        · simp only [Category.assoc, lift_snd, associator_hom_snd_snd]
    have e := hmul h h' x
    rw [hl, ← lift_whiskerLeft_assoc, ha] at e
    exact e

/-- The construction retains exactly the supplied action morphism. -/
theorem schemeActionOfPointLaws_smul (hom : H.X ⊗ X ⟶ X)
    (hone : ∀ {T : Over S} (x : T ⟶ X),
      lift (1 : T ⟶ H.X) x ≫ hom = x)
    (hmul : ∀ {T : Over S} (h h' : T ⟶ H.X) (x : T ⟶ X),
      lift (h * h') x ≫ hom = lift h (lift h' x ≫ hom) ≫ hom) :
    letI := schemeActionOfPointLaws hom hone hmul
    γ[H.X, X] = hom := rfl

end Langlands.GroupScheme
