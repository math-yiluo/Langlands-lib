import Langlands.Representation.Archimedean.SmoothCasselmanWallachStatement

/-! # The Harish-Chandra module of compact-finite genuine smooth Hilbert vectors -/

noncomputable section

universe uH
open scoped TensorProduct Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

/-- **Harish-Chandra module of an irreducible admissible Hilbert representation of real
`GL_(r+1)`.** For every jointly continuous, topologically irreducible and compact
admissible representation `R` of actual `GL_(r+1)(ℝ)` on a complete complex Hilbert
space, the compact-finite genuine smooth vectors carry an algebraically irreducible
admissible `(𝔤𝔩_(r+1)(ℝ), O(r+1))`-module structure whose compact action is the actual
orthogonal action and whose action of each complexified real matrix `1 ⊗ X` is the
genuine derivative along `X`. -/
def RealSmoothHilbertHarishChandraModuleStatement : Prop :=
  ∀ (r : ℕ) (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (R : Langlands.GeneralLinear (r + 1) ℝ →* (H →L[ℂ] H)),
    IsIrreducibleAdmissibleHilbertRepresentation ℝ (r + 1) R →
      ∃ (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℝ)
            (smoothHilbertKFinite ℝ (r + 1) R))
        (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) →ₗ⁅ℂ⁆
            Module.End ℂ (smoothHilbertKFinite ℝ (r + 1) R)),
        IsRealGKModule (r + 1) ρ π ∧ IsIrreducibleGKModule ρ π ∧
          IsAdmissibleGKModule ρ ∧
          IsSmoothGKIntertwiner ℝ (r + 1) R ρ π (smoothHilbertKFinite ℝ (r + 1) R).subtype

end Langlands.Archimedean
