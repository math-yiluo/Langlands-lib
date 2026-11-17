import Langlands.Representation.Archimedean.TransposePairing

/-! # Archimedean inverse-transpose pairing existence -/

noncomputable section
universe uV
set_option autoImplicit false
open scoped TensorProduct

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The real inverse-transpose pairing obligation: every irreducible admissible
`(𝔤𝔩_(r+1)(ℝ), O(r+1))`-module has a nonzero complex bilinear pairing with its
inverse-transpose twist. No genericity or unitarity hypothesis is imposed. -/
def RealTransposePairingStatement : Prop :=
  ∀ (r : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V),
    IsRealGKModule (r + 1) ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      HasNonzeroTransposeGKPairing ℝ (r + 1) ρ π

/-- The complex inverse-transpose pairing obligation for an irreducible
admissible `(𝔤𝔩_(r+1)(ℂ), U(r+1))`-module. The Lie algebra is the
complexification of the underlying real matrix Lie algebra. -/
def ComplexTransposePairingStatement : Prop :=
  ∀ (r : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℂ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V),
    IsComplexGKModule (r + 1) ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      HasNonzeroTransposeGKPairing ℂ (r + 1) ρ π

/-- The real and complex local pairing obligations needed for the
archimedean part of the cuspidal inverse-transpose argument. -/
def ArchimedeanTransposePairingStatement : Prop :=
  RealTransposePairingStatement.{uV} ∧ ComplexTransposePairingStatement.{uV}

end Langlands.Archimedean
