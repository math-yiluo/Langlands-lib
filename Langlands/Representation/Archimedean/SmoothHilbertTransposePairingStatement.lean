import Langlands.Representation.Archimedean.SmoothHilbert

/-! # Smooth Hilbert inverse-transpose pairing targets -/

noncomputable section

universe uH
open scoped Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

/-- On the genuine smooth vectors of every irreducible admissible continuous complete
complex Hilbert representation of actual `GL_(r+1)(ℝ)`, a nonzero separately continuous
complex bilinear inverse-transpose invariant form exists. -/
def RealSmoothHilbertTransposePairingStatement : Prop :=
  ∀ (r : ℕ) (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (R : Langlands.GeneralLinear (r + 1) ℝ →* (H →L[ℂ] H)),
    IsIrreducibleAdmissibleHilbertRepresentation ℝ (r + 1) R →
      HasNonzeroSmoothHilbertTransposePairing ℝ (r + 1) R

/-- The analogous smooth pairing for actual `GL_(r+1)(ℂ)`, using ordinary inverse
transpose and the genuine real word-derivative topology. -/
def ComplexSmoothHilbertTransposePairingStatement : Prop :=
  ∀ (r : ℕ) (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (R : Langlands.GeneralLinear (r + 1) ℂ →* (H →L[ℂ] H)),
    IsIrreducibleAdmissibleHilbertRepresentation ℂ (r + 1) R →
      HasNonzeroSmoothHilbertTransposePairing ℂ (r + 1) R

/-- The real and complex smooth Hilbert pairing obligations, in every carrier universe. -/
def ArchimedeanSmoothHilbertTransposePairingStatement : Prop :=
  RealSmoothHilbertTransposePairingStatement.{uH} ∧
    ComplexSmoothHilbertTransposePairingStatement.{uH}

end Langlands.Archimedean
