import Langlands.GroupScheme.ConjugacyBaseChange
import Langlands.Shimura.Unitary.ComplexCocharacterConjugacy

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Algebra
open scoped CategoryTheory.MonObj

namespace Langlands.Shimura.CentralSimpleUnitaryData
variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)

omit [IsScalarTower E K A] in
/-- Actual rational Galois transport preserves scheme inner conjugacy. -/
theorem galoisCocharacter_conjugate (s : ℂ ≃ₐ[ℚ] ℂ)
    {χ ψ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶
      D.complexRationalGroupScheme} (h : D.ComplexCocharacterConjugate χ ψ) :
    D.ComplexCocharacterConjugate (D.galoisCocharacter s χ) (D.galoisCocharacter s ψ) :=
  ((h.postcomp D.complexDirectGroupSchemeIso.hom).transportCocharacter
    rationalComplexBaseMap (complexGaloisBaseMap s) (complexGaloisBaseMap_over s)
    D.rationalGroupScheme).postcomp D.complexDirectGroupSchemeIso.inv

omit [IsScalarTower E K A] in
/-- Galois transport also reflects inner conjugacy, by applying the inverse automorphism. -/
theorem galoisCocharacter_conjugate_iff (s : ℂ ≃ₐ[ℚ] ℂ)
    (χ ψ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶
      D.complexRationalGroupScheme) :
    D.ComplexCocharacterConjugate (D.galoisCocharacter s χ) (D.galoisCocharacter s ψ) ↔
      D.ComplexCocharacterConjugate χ ψ := by
  constructor
  · intro h
    have hi := D.galoisCocharacter_conjugate s⁻¹ h
    simpa only [← D.galoisCocharacter_mul, inv_mul_cancel, D.galoisCocharacter_one] using hi
  · exact D.galoisCocharacter_conjugate s

/-- The Galois subgroup stabilizing the inner-conjugacy class of an actual scheme cocharacter. -/
def complexCocharacterStabilizer
    (χ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶
      D.complexRationalGroupScheme) : Subgroup (ℂ ≃ₐ[ℚ] ℂ) where
  carrier := {s | D.ComplexCocharacterConjugate (D.galoisCocharacter s χ) χ}
  one_mem' := by
    change D.ComplexCocharacterConjugate (D.galoisCocharacter 1 χ) χ
    rw [D.galoisCocharacter_one]
    exact GroupScheme.HomConjugate.refl χ
  mul_mem' := by
    intro s t hs ht
    change D.ComplexCocharacterConjugate (D.galoisCocharacter (s * t) χ) χ
    rw [D.galoisCocharacter_mul]
    exact (D.galoisCocharacter_conjugate s ht).trans hs
  inv_mem' := by
    intro s hs
    have h := D.galoisCocharacter_conjugate s⁻¹ hs
    rw [← D.galoisCocharacter_mul, inv_mul_cancel, D.galoisCocharacter_one] at h
    exact h.symm

omit [IsScalarTower E K A] in
@[simp] theorem mem_complexCocharacterStabilizer
    (χ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶
      D.complexRationalGroupScheme) (s : ℂ ≃ₐ[ℚ] ℂ) :
    s ∈ D.complexCocharacterStabilizer χ ↔
      D.ComplexCocharacterConjugate (D.galoisCocharacter s χ) χ := Iff.rfl

omit [IsScalarTower E K A] in
/-- Conjugate cocharacters have the same actual Galois stabilizer. -/
theorem complexCocharacterStabilizer_eq_of_conjugate
    {χ ψ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶
      D.complexRationalGroupScheme} (h : D.ComplexCocharacterConjugate χ ψ) :
    D.complexCocharacterStabilizer χ = D.complexCocharacterStabilizer ψ := by
  ext s
  change D.ComplexCocharacterConjugate (D.galoisCocharacter s χ) χ ↔
    D.ComplexCocharacterConjugate (D.galoisCocharacter s ψ) ψ
  constructor
  · intro hs
    exact ((D.galoisCocharacter_conjugate s h.symm).trans hs).trans h
  · intro hs
    exact ((D.galoisCocharacter_conjugate s h).trans hs).trans h.symm

/-- The intermediate field fixed by the actual scheme-conjugacy stabilizer. -/
def complexCocharacterFixedField
    (χ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶
      D.complexRationalGroupScheme) : IntermediateField ℚ ℂ :=
  IntermediateField.fixedField (D.complexCocharacterStabilizer χ)

omit [IsScalarTower E K A] in
/-- Membership is fixation by every automorphism preserving the actual conjugacy class. -/
theorem mem_complexCocharacterFixedField
    (χ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶
      D.complexRationalGroupScheme) (z : ℂ) :
    z ∈ D.complexCocharacterFixedField χ ↔
      ∀ s : ℂ ≃ₐ[ℚ] ℂ,
        D.ComplexCocharacterConjugate (D.galoisCocharacter s χ) χ → s z = z := by
  exact IntermediateField.mem_fixedField_iff _ _

omit [IsScalarTower E K A] in
/-- The constructed field depends only on the inner-conjugacy class. -/
theorem complexCocharacterFixedField_eq_of_conjugate
    {χ ψ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶
      D.complexRationalGroupScheme} (h : D.ComplexCocharacterConjugate χ ψ) :
    D.complexCocharacterFixedField χ = D.complexCocharacterFixedField ψ := by
  unfold complexCocharacterFixedField
  rw [D.complexCocharacterStabilizer_eq_of_conjugate h]

variable {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

/-- The fixed field of the actual first-factor Kottwitz scheme-cocharacter class. -/
def kottwitzCocharacterReflexField : IntermediateField ℚ ℂ :=
  D.complexCocharacterFixedField (D.kottwitzCocharacter C true)

end Langlands.Shimura.CentralSimpleUnitaryData
