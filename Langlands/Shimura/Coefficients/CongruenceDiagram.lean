import Langlands.CategoryTheory.EquivariantDiagram
import Langlands.Shimura.Coefficients.FiniteQuotient

/-! # The actual congruence coefficient diagram over its varying groups -/

noncomputable section

universe u v w

namespace Langlands.Shimura.Coefficients

open CategoryTheory Opposite

variable {R : Type v} [CommRing R] {G : Type w} [Group G]
variable (I : Ideal R) (M : Action (ModuleCat.{u} R) G)

/-- The actual torsion modules, acted on by their respective congruence quotients.
All transitions are the published ideal-power quotient maps. -/
def congruenceCoefficientDiagram :
    EquivariantDiagram (torsionCongruenceGroups I M) (ModuleCat.{u} R) where
  obj := torsionSystem I M ⋙ Action.forget (ModuleCat.{u} R) G
  ρ n := (quotientTorsionAction I M n.unop
    (congruenceKernel I M n.unop) le_rfl).ρ
  comm := by
    intro i j f g
    induction g using QuotientGroup.induction_on with
    | H g =>
      exact ((torsionSystem I M).map f).comm g

/-- At each level the representation is the published action factored by its kernel. -/
@[simp] theorem congruenceCoefficientDiagram_action (n : ℕᵒᵖ) :
    (congruenceCoefficientDiagram I M).action n =
      quotientTorsionAction I M n.unop (congruenceKernel I M n.unop) le_rfl := rfl

/-- The underlying transition remains the original coefficient reduction. -/
@[simp] theorem congruenceCoefficientDiagram_transition_hom
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ((congruenceCoefficientDiagram I M).transition f).hom =
      ((torsionSystem I M).map f).hom := rfl

/-- These quotient-module transitions are surjective. -/
theorem congruenceCoefficientDiagram_transition_surjective
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    Function.Surjective ((congruenceCoefficientDiagram I M).transition f).hom :=
  torsion_transition_surjective I M (leOfHom f.unop)

end Langlands.Shimura.Coefficients
