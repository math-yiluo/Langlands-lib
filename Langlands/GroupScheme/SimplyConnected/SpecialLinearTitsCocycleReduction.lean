import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocycleStarComparison
import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocycleMatrixFormulas
import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocyclePresentationWeights

/-! # Reduction of the Tits cocycle presentation to special-linear automorphisms -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SpecialLinearTitsCocycle

variable {K : Type u} [Field K]
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {d : TitsIndexData G} {n : ℕ} {e : d.Vertex ≃ Fin n}

/-- The two all-test discrepancy formulas classified by the original Tits star action,
for a supplied coordinate presentation and family of matrices. -/
def Presentation.HasTitsMatrixFormulas (p : Presentation d e)
    (x : (p.L ≃ₐ[K] p.L) → Matrix.GeneralLinearGroup (Fin (n + 1)) p.L) : Prop :=
  ∀ (σ : p.L ≃ₐ[K] p.L) (τ : SeparableClosure K ≃ₐ[K] SeparableClosure K),
    (∀ y, τ (p.embedding y) = p.embedding (σ y)) →
    ∀ (Z : Over (Spec (CommRingCat.of K))) (a : Z ⟶ cover K p.L)
      (g : Matrix.SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)),
      ((∀ v, d.star τ v = v) →
        (discrepancy p.localIso σ a g :
            Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
          (Matrix.GeneralLinearGroup.map (coefficients a) (x σ) :
              Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) *
            (g : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) *
            (Matrix.GeneralLinearGroup.map (coefficients a) (x σ)⁻¹ :
              Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤))) ∧
      ((∃ v, d.star τ v ≠ v) →
        (discrepancy p.localIso σ a g :
            Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
          (Matrix.GeneralLinearGroup.map (coefficients a) (x σ) :
              Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) *
            ((g⁻¹ : Matrix.SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
              Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)).transpose *
            (Matrix.GeneralLinearGroup.map (coefficients a) (x σ)⁻¹ :
              Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)))

/-- The conditional discrepancy matrices satisfy the formulas for the original
Tits star action and every specified lift. -/
theorem Presentation.hasTitsMatrixFormulas_discrepancyMatrices (p : Presentation d e)
    (hAut : SpecialLinearTorusAutomorphismStatement.{u}) :
    p.HasTitsMatrixFormulas (p.discrepancyMatrices hAut) := by
  intro σ τ hστ Z a g
  have hx := (p.exists_discrepancy_matrices hAut).choose_spec σ Z a g
  constructor
  · intro hfix
    exact hx.1 ((p.discrepancyBasedAction_fixes_iff_star σ τ hστ).mpr hfix)
  · intro hmove
    exact hx.2 ((p.discrepancyBasedAction_moves_iff_star σ τ hστ).mpr hmove)

end SpecialLinearTitsCocycle

/-- The all-test special-linear automorphism theorem suffices for the exact
Galois-twisted special-linear Tits presentation. -/
theorem specialLinearTitsCocycle_of_torusAutomorphism
    (hAut : SpecialLinearTorusAutomorphismStatement.{u}) :
    SpecialLinearTitsCocycleStatement.{u} := by
  intro K _ G _ _ d n e hG _ hcartan
  obtain ⟨p⟩ := SpecialLinearTitsCocycle.exists_presentation (d := d) (e := e) hG hcartan
  exact ⟨p.L, inferInstance, inferInstance, inferInstance, inferInstance,
    p.embedding, p.localIso, p.discrepancyMatrices hAut, p.diagonalWeights,
    p.hasTitsMatrixFormulas_discrepancyMatrices hAut, p.diagonal,
    p.rootRestriction_diagonalWeights⟩

end Langlands.GroupScheme
