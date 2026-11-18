import Langlands.Representation.Archimedean.SmoothHilbert

/-! # Hilbert globalization targets for every irreducible admissible algebraic GL module -/

noncomputable section

universe uV
open scoped TensorProduct Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Every irreducible admissible real general linear GK module has a Hilbert
realization with a dense compact-finite identification and genuine derivative comparisons. -/
def RealHilbertGlobalizationStatement : Prop :=
  ∀ (r : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V),
    IsRealGKModule (r + 1) ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      ∃ (H : Type uV) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
        (_ : CompleteSpace H) (R : Langlands.GeneralLinear (r + 1) ℝ →* (H →L[ℂ] H))
        (e : V ≃ₗ[ℂ] smoothHilbertKFinite ℝ (r + 1) R),
        IsSmoothHilbertGlobalization ℝ (r + 1) R ρ π e

/-- The analogous Hilbert realization for complex general linear GK modules.
The Lie algebra and orbit directions are taken over the underlying real matrix space. -/
def ComplexHilbertGlobalizationStatement : Prop :=
  ∀ (r : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℂ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V),
    IsComplexGKModule (r + 1) ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      ∃ (H : Type uV) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
        (_ : CompleteSpace H) (R : Langlands.GeneralLinear (r + 1) ℂ →* (H →L[ℂ] H))
        (e : V ≃ₗ[ℂ] smoothHilbertKFinite ℂ (r + 1) R),
        IsSmoothHilbertGlobalization ℂ (r + 1) R ρ π e

/-- The real and complex Hilbert globalization obligations, at any carrier universe. -/
def ArchimedeanHilbertGlobalizationStatement : Prop :=
  RealHilbertGlobalizationStatement.{uV} ∧ ComplexHilbertGlobalizationStatement.{uV}

end Langlands.Archimedean
