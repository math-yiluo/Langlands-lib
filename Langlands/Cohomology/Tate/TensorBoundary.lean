import Langlands.Cohomology.Tate.TensorNaturality
import Langlands.Cohomology.Tate.DoubleBoundary

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory TensorProduct

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G]

/-- The commuting coefficient diagram obtained by tensoring two short complexes. -/
def tensorGrid (S T : ShortComplex (Rep.{u} R G)) :
    ShortComplex (ShortComplex (Rep.{u} R G)) where
  X₁ := T.map (MonoidalCategory.tensorLeft S.X₁)
  X₂ := T.map (MonoidalCategory.tensorLeft S.X₂)
  X₃ := T.map (MonoidalCategory.tensorLeft S.X₃)
  f := tensorSequenceMapLeft (𝟙 T) S.f
  g := tensorSequenceMapLeft (𝟙 T) S.g
  zero := by
    apply ShortComplex.hom_ext
    all_goals
      change (_ ⊗ₘ 𝟙 _) ≫ (_ ⊗ₘ 𝟙 _) = 0
      simp only [MonoidalCategory.tensorHom_comp_tensorHom, S.zero, Category.id_comp]
      simp

lemma tensorGrid_column₁ (S T : ShortComplex (Rep.{u} R G)) :
    (tensorGrid S T).map ShortComplex.π₁ = S.map (MonoidalCategory.tensorRight T.X₁) := rfl

lemma tensorGrid_column₂ (S T : ShortComplex (Rep.{u} R G)) :
    (tensorGrid S T).map ShortComplex.π₂ = S.map (MonoidalCategory.tensorRight T.X₂) := rfl

lemma tensorGrid_column₃ (S T : ShortComplex (Rep.{u} R G)) :
    (tensorGrid S T).map ShortComplex.π₃ = S.map (MonoidalCategory.tensorRight T.X₃) := rfl

variable [Fintype G]

/-- The two actual Tate boundaries on a tensor diagram anticommute under exact tensor hypotheses. -/
lemma tensor_delta_anticommutes (S T : ShortComplex (Rep.{u} R G))
    (hTop : (T.map (MonoidalCategory.tensorLeft S.X₁)).ShortExact)
    (hBottom : (T.map (MonoidalCategory.tensorLeft S.X₃)).ShortExact)
    (hLeft : (S.map (MonoidalCategory.tensorRight T.X₁)).ShortExact)
    (hMiddle : (S.map (MonoidalCategory.tensorRight T.X₂)).ShortExact)
    (hRight : (S.map (MonoidalCategory.tensorRight T.X₃)).ShortExact) (n : ℤ) :
    TateCohomology.δ hBottom n ≫ TateCohomology.δ hLeft (n + 1) =
      -(TateCohomology.δ hRight n ≫ TateCohomology.δ hTop (n + 1)) := by
  let F := (tateComplexFunctor R G).mapShortComplex
  let : F.PreservesZeroMorphisms := ⟨fun X Y => by
    apply ShortComplex.hom_ext
    all_goals exact Functor.map_zero (tateComplexFunctor R G) _ _⟩
  let D := (tensorGrid S T).map F
  have h₁ : D.X₁.ShortExact := TateCohomology.map_tateComplexFunctor_shortExact hTop
  have h₃ : D.X₃.ShortExact := TateCohomology.map_tateComplexFunctor_shortExact hBottom
  have e₁ : D.map ShortComplex.π₁ =
      ((tensorGrid S T).map ShortComplex.π₁).map (tateComplexFunctor R G) := rfl
  have e₂ : D.map ShortComplex.π₂ =
      ((tensorGrid S T).map ShortComplex.π₂).map (tateComplexFunctor R G) := rfl
  have e₃ : D.map ShortComplex.π₃ =
      ((tensorGrid S T).map ShortComplex.π₃).map (tateComplexFunctor R G) := rfl
  rw [tensorGrid_column₁] at e₁
  rw [tensorGrid_column₂] at e₂
  rw [tensorGrid_column₃] at e₃
  have hc₁ : (D.map ShortComplex.π₁).ShortExact := by
    rw [e₁]
    exact TateCohomology.map_tateComplexFunctor_shortExact hLeft
  have hc₂ : (D.map ShortComplex.π₂).ShortExact := by
    rw [e₂]
    exact TateCohomology.map_tateComplexFunctor_shortExact hMiddle
  have hc₃ : (D.map ShortComplex.π₃).ShortExact := by
    rw [e₃]
    exact TateCohomology.map_tateComplexFunctor_shortExact hRight
  have h := doubleBoundary_anticommutes D h₁ h₃ hc₁ hc₂ hc₃ n
  exact h

end Langlands.Tate
