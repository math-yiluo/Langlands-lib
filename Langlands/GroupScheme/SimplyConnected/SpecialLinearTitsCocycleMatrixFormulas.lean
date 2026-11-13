import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocycleMatrixDiscrepancy
import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocycleDiscrepancy
import Langlands.GroupScheme.Reductive.SpecialLinearTorusAutomorphismStatement

/-! # Conditional matrix formulas on every Galois-cover test -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinearTitsCocycle

variable {K : Type u} [Field K]
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {d : TitsIndexData G} {n : ℕ} {e : d.Vertex ≃ Fin n}

private theorem Presentation.localIso_def (p : Presentation d e) :
    p.localIso = LocalGroupIso.ofBaseChangeIso p.baseChangeIso := rfl

private theorem Presentation.discrepancyIso_def (p : Presentation d e)
    (σ : p.L ≃ₐ[K] p.L) :
    p.discrepancyIso σ = matrixDiscrepancyIso p.baseChangeIso σ := rfl

/-- The coordinate discrepancy evaluates to the original local discrepancy on every
relative test carrying a point of the Galois cover. -/
theorem Presentation.discrepancy_eq_discrepancyIso (p : Presentation d e)
    (σ : p.L ≃ₐ[K] p.L) {Z : Over (Spec (CommRingCat.of K))}
    (a : Z ⟶ cover K p.L)
    (g : Matrix.SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
    discrepancy p.localIso σ a g =
      SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of p.L)
        (LocalGroupIso.coverTest a)
        (((SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of p.L)
          (LocalGroupIso.coverTest a)).symm g) ≫
            (p.discrepancyIso σ).hom.hom.hom) := by
  rw [p.localIso_def, p.discrepancyIso_def]
  exact discrepancy_eq_matrixDiscrepancyIso p.baseChangeIso σ a g

/-- The torus-automorphism classification, if supplied, gives a simultaneous choice
of discrepancy matrices and the two formulas on every cover test. The premises
refer to the actual based projection of the coordinate discrepancy root action. -/
theorem Presentation.exists_discrepancy_matrices (p : Presentation d e)
    (hAut : SpecialLinearTorusAutomorphismStatement.{u}) :
    ∃ x : (p.L ≃ₐ[K] p.L) → Matrix.GeneralLinearGroup (Fin (n + 1)) p.L,
      ∀ σ : p.L ≃ₐ[K] p.L,
        let q := p.coordinatePinning
        let δ := rootDatumEquivOfTorusCompatibleIso
          q.isConnectedReductive q.isConnectedReductive
          q.isSplitTorus q.isSplitTorus q.isMaximalTorus q.isMaximalTorus
          (p.discrepancyIso σ) (p.discrepancyTorusIso σ) (p.discrepancy_square σ)
          q.isRootDatum q.isRootDatum
        let θ := q.basedRootDatumProjection δ
        ∀ (Z : Over (Spec (CommRingCat.of K))) (a : Z ⟶ cover K p.L)
          (g : Matrix.SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)),
          ((∀ v : q.base.support, θ.val.indexEquiv v.val = v.val) →
            (discrepancy p.localIso σ a g :
                Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
              (Matrix.GeneralLinearGroup.map (coefficients a) (x σ) :
                  Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) *
                (g : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) *
                (Matrix.GeneralLinearGroup.map (coefficients a) (x σ)⁻¹ :
                  Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤))) ∧
          ((∃ v : q.base.support, θ.val.indexEquiv v.val ≠ v.val) →
            (discrepancy p.localIso σ a g :
                Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
              (Matrix.GeneralLinearGroup.map (coefficients a) (x σ) :
                  Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) *
                ((g⁻¹ : Matrix.SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
                  Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)).transpose *
                (Matrix.GeneralLinearGroup.map (coefficients a) (x σ)⁻¹ :
                  Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤))) := by
  classical
  have hmatrix (σ : p.L ≃ₐ[K] p.L) :=
    hAut p.L n p.coordinatePinning (p.discrepancyIso σ)
      (p.discrepancyTorusIso σ) (p.discrepancy_square σ)
  choose x hx using hmatrix
  refine ⟨x, ?_⟩
  intro σ
  dsimp only
  intro Z a g
  have h := hx σ (LocalGroupIso.coverTest a) g
  constructor
  · intro hfix
    rw [p.discrepancy_eq_discrepancyIso σ a g]
    have h' := h.1 hfix
    rw [scalarMap_coverTest, Matrix.GeneralLinearGroup.map_inv] at h'
    exact h'
  · intro hmove
    rw [p.discrepancy_eq_discrepancyIso σ a g]
    have h' := h.2 hmove
    rw [scalarMap_coverTest, Matrix.GeneralLinearGroup.map_inv] at h'
    exact h'

/-- A choice of the simultaneous discrepancy matrices from the conditional
all-cover-test formula theorem. -/
def Presentation.discrepancyMatrices (p : Presentation d e)
    (hAut : SpecialLinearTorusAutomorphismStatement.{u}) :
    (p.L ≃ₐ[K] p.L) → Matrix.GeneralLinearGroup (Fin (n + 1)) p.L :=
  (p.exists_discrepancy_matrices hAut).choose

end Langlands.GroupScheme.SpecialLinearTitsCocycle
