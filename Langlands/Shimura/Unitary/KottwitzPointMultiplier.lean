import Langlands.Shimura.Unitary.ComplexAffineKottwitz
import Langlands.Shimura.Unitary.ComplexCocharacterPoints

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Algebra Matrix
open scoped CategoryTheory.MonObj Classical TensorProduct

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
  (hΦ : IsCMSection E K Φ)

set_option backward.isDefEq.respectTransparency false in
/-- Rational affine multiplier is normalization of the complex test-section multiplier. -/
theorem complexPointMultiplier_affine
    (x : (algSpec (CommRingCat.of ℂ)).obj (op (CommAlgCat.of ℂ ℂ)) ⟶
      D.complexRationalGroupScheme.X) :
    D.complexPointMultiplier (D.complexAffineRationalPoint ℂ x) =
      Units.map (GroupScheme.Corepresented.affineSectionsAlgEquiv
        (R := CommRingCat.of ℂ) (CommAlgCat.of ℂ ℂ)).toMonoidHom
          (D.complexGroupPointsEquiv C _ x).2 := by
  calc
    _ = ((D.toSecondKindInvolution.rationalInvolution.baseChange ℝ).baseChange ℂ).multiplier
        (D.complexAffineSimilitudes ℂ x) := by
      rw [D.complexAffineSimilitudes_tower]
      exact Units.ext rfl
    _ = _ := by
      exact Units.ext rfl

/-- The multiplier of each rational-model Kottwitz value is the inverse input unit. -/
theorem complexPointMultiplier_kottwitzCocharacterValue (first : Bool) (u : ℂˣ) :
    D.complexPointMultiplier (D.complexCocharacterValue (D.kottwitzCocharacter C first) u) =
      u⁻¹ := by
  rw [← D.complexAffineCocharacterValue_rational, D.complexPointMultiplier_affine C,
    complexAffineCocharacterValue, D.kottwitzCocharacter_split_multiplier]
  apply Units.ext
  exact GroupScheme.Gm.relativeAffineUnitPoint_inverse_sections ℂ ℂ u

/-- Galois transport preserves the inverse-unit multiplier of the Kottwitz family. -/
theorem complexPointMultiplier_galois_kottwitz (s : ℂ ≃ₐ[ℚ] ℂ)
    (first : Bool) (u : ℂˣ) :
    D.complexPointMultiplier
      (D.complexCocharacterValue (D.galoisCocharacter s (D.kottwitzCocharacter C first)) u) =
      u⁻¹ := by
  rw [D.complexCocharacterValue_galois_comparison,
    D.directComplexCocharacterValue_transport, D.complexPointMultiplier_galois]
  change Units.map s.toMonoidHom
    (D.complexPointMultiplier
      (D.complexCocharacterValue (D.kottwitzCocharacter C first)
        (Units.map s.symm.toMonoidHom u))) = _
  rw [D.complexPointMultiplier_kottwitzCocharacterValue C]
  apply Units.ext
  simp

end Langlands.Shimura.CentralSimpleUnitaryData
