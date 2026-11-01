import Langlands.AlgebraicGeometry.Modules.CoherentEulerPolynomial
import Langlands.AlgebraicGeometry.Picard.EulerPositivityPreparationProof
import Langlands.Algebra.RationalPolynomialDilationProof

/-! # The positive dimension-zero coherent Euler polynomial -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

open Langlands.Scheme.Modules

variable {X : Scheme.{u}} {K : Type u} [Field K]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]

/-- The constant polynomial associated to the actual coherent Euler characteristic. -/
def coherentEulerConstantPolynomial (M : X.Modules) [M.IsQuasicoherent]
    (hM : HasFiniteAffineSections M) : Polynomial ℚ :=
  C (coherentEulerCharacteristic f M hM : ℚ)

/-- At exponent zero the twisted Euler sequence is the original Euler characteristic. -/
lemma coherentEulerSequence_eval_zero (M : X.Modules) [M.IsQuasicoherent]
    (hM : HasFiniteAffineSections M) (L : Picard.LineBundle X) :
    coherentEulerSequence f M hM L 0 = (coherentEulerCharacteristic f M hM : ℚ) := by
  have hL := Picard.tensorPow_isLocallyFreeRankOne X L 0
  have := QuasicoherentLocal.isQuasicoherent_tensor_lineBundle M _ hL
  change (coherentEulerCharacteristic f (tensorObj M (tensorPow L.obj 0))
    (hM.tensor_lineBundle hL) : ℚ) = _
  exact congrArg (Int.cast : ℤ → ℚ)
    (coherentEulerCharacteristic_iso f (hM.tensor_lineBundle hL) hM (tensorRightUnitor M))

/-- The zeroth Newton truncation is the constant original Euler characteristic. -/
lemma coherentEulerPolynomial_zero_eq_C (M : X.Modules) [M.IsQuasicoherent]
    (hM : HasFiniteAffineSections M) (L : Picard.LineBundle X) :
    coherentEulerPolynomial f M hM L 0 = coherentEulerConstantPolynomial f M hM := by
  simp [coherentEulerPolynomial, Langlands.Algebra.RationalPolynomial.newtonPolynomial,
    coherentEulerSequence_eval_zero, coherentEulerConstantPolynomial]

variable [IsNoetherian X] [X.IsSeparated]

/-- With support dimension at most zero every truncation is the same constant polynomial. -/
theorem coherentEulerPolynomial_eq_C_of_supportDimensionLT_one
    (M : X.Modules) [M.IsQuasicoherent] (hM : HasFiniteAffineSections M)
    (L : Picard.LineBundle X) (d : ℕ) (hS : HasSupportDimensionLT M 1) :
    coherentEulerPolynomial f M hM L d = coherentEulerConstantPolynomial f M hM := by
  apply Langlands.Algebra.RationalPolynomial.eq_of_eventually_nat_eval_eq
  apply Filter.Eventually.of_forall
  intro n
  rw [coherentEulerPolynomial_eval f M hM L d (hS.mono (by omega)),
    ← coherentEulerPolynomial_eval f M hM L 0 (by simpa using hS) n,
    coherentEulerPolynomial_zero_eq_C]

omit [X.IsSeparated] in
/-- The constant coefficient is positive exactly when the dimension-zero sheaf is nonzero. -/
theorem coherentEulerCharacteristic_pos_iff_of_supportDimensionLT_one
    (M : X.Modules) [M.IsQuasicoherent] (hM : HasFiniteAffineSections M)
    (hS : HasSupportDimensionLT M 1) :
    0 < coherentEulerCharacteristic f M hM ↔ ¬ IsZero M :=
  Picard.eulerCharacteristic_pos_iff_of_finiteClosedSupport f M
    (hasFiniteCohomology_of_coherent f M hM) hS.hasFiniteClosedSupport

/-- The dimension-zero polynomial has positive leading coefficient precisely for a nonzero sheaf. -/
theorem coherentEulerPolynomial_leadingCoeff_pos_iff_of_supportDimensionLT_one
    (M : X.Modules) [M.IsQuasicoherent] (hM : HasFiniteAffineSections M)
    (L : Picard.LineBundle X) (d : ℕ) (hS : HasSupportDimensionLT M 1) :
    0 < (coherentEulerPolynomial f M hM L d).leadingCoeff ↔ ¬ IsZero M := by
  rw [coherentEulerPolynomial_eq_C_of_supportDimensionLT_one f M hM L d hS,
    coherentEulerConstantPolynomial, leadingCoeff_C, Int.cast_pos]
  exact coherentEulerCharacteristic_pos_iff_of_supportDimensionLT_one f M hM hS

/-- A nonzero dimension-zero coherent sheaf has exact Euler degree zero and positive leading term. -/
theorem coherentEulerPolynomial_natDegree_eq_zero_and_leadingCoeff_pos
    (M : X.Modules) [M.IsQuasicoherent] (hM : HasFiniteAffineSections M)
    (L : Picard.LineBundle X) (d : ℕ) (hS : HasSupportDimensionLT M 1)
    (hne : ¬ IsZero M) :
    (coherentEulerPolynomial f M hM L d).natDegree = 0 ∧
      0 < (coherentEulerPolynomial f M hM L d).leadingCoeff := by
  refine ⟨?_, (coherentEulerPolynomial_leadingCoeff_pos_iff_of_supportDimensionLT_one
    f M hM L d hS).2 hne⟩
  rw [coherentEulerPolynomial_eq_C_of_supportDimensionLT_one f M hM L d hS,
    coherentEulerConstantPolynomial, natDegree_C]

end Langlands.AlgebraicGeometry.Modules.DerivedSections
