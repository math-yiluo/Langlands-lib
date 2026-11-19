import Langlands.Representation.Archimedean.RealCompactPolynomialFullBraidProof
import Langlands.Representation.Archimedean.RealGenericCharacterBraidReduction

/-! # Full polynomial braid on finite compact degree spaces -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealCompactCharacterPolynomialBraid

open Complex Polynomial RealCompactPolynomialFourierRelation RealOrthogonalUncertainty
  RealCompactPolynomialRelations RealTailMultiplierPolynomial

theorem normalized_braid {A : Type} [Ring A] [Algebra ℂ A] {X Y Z : A}
    (hXY : X * Y - Y * X = Z) (hZX : Z * X - X * Z = Y)
    (hZY : Z * Y - Y * Z = -X) (n m : ℕ) :
    aeval ((-I : ℂ) • X) (tailPolynomial n) *
        aeval ((-I : ℂ) • Y) (tailPolynomial (n + m)) *
        aeval ((-I : ℂ) • X) (tailPolynomial m) =
      aeval ((-I : ℂ) • Y) (tailPolynomial m) *
        aeval ((-I : ℂ) • X) (tailPolynomial (n + m)) *
        aeval ((-I : ℂ) • Y) (tailPolynomial n) := by
  have hf := realCompactPolynomialFullBraid A X Y Z hXY hZX hZY n m
  simp_rw [RealTailCompactPolynomialNormalization.operator_eq_factor]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [hf]
  congr 1
  ring

set_option maxHeartbeats 850000 in
theorem polynomial_braid (N n m : ℕ) :
    RealGenericCharacterBraidReduction.PolynomialBraid N n m := by
  have hp0 : 0 + 1 < 3 := by decide
  have hp1 : 1 + 1 < 3 := by decide
  obtain ⟨Z, hXY, hYZ, hZX⟩ := exists_relations N (Or.inl ⟨rfl, rfl⟩) hp0 hp1
  have hZY : Z * gen N hp1 - gen N hp1 * Z = -gen N hp0 := by
    apply LinearMap.ext
    intro w
    have h := LinearMap.congr_fun hYZ w
    change gen N hp1 (Z w) - Z (gen N hp1 w) = gen N hp0 w at h
    change Z (gen N hp1 w) - gen N hp1 (Z w) = -(gen N hp0 w)
    rw [← h]
    abel
  simpa only [RealGenericCharacterBraidReduction.PolynomialBraid] using
    (normalized_braid (X := gen N hp0) (Y := gen N hp1) hXY hZX hZY n m)

end Langlands.Archimedean.RealCompactCharacterPolynomialBraid
