import Langlands.Shimura.Unitary.GaloisCocharacterEvaluationStatement

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Algebra
open scoped CategoryTheory.MonObj

namespace Langlands.Shimura.CentralSimpleUnitaryData
variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)

set_option maxHeartbeats 10000 in
omit [IsScalarTower E K A] in
/-- Galois transport evaluates by the inverse-input, forward-output formula. -/
theorem complexCocharacterValue_galois (s : ℂ ≃ₐ[ℚ] ℂ)
    (χ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶ D.complexRationalGroupScheme)
    (u : ℂˣ) :
    D.complexCocharacterValue (D.galoisCocharacter s χ) u =
      D.complexPointGaloisAction s
        (D.complexCocharacterValue χ (Units.map s.symm.toMonoidHom u)) := by
  exact (D.complexCocharacterValue_galois_comparison s χ u).trans
    ((D.directComplexCocharacterValue_transport s (χ ≫ D.complexDirectGroupSchemeIso.hom) u).trans
      (congrArg (D.complexPointGaloisAction s)
        (D.complexCocharacterValue_comparison χ (Units.map s.symm.toMonoidHom u)).symm))

set_option maxHeartbeats 10000 in
omit [IsScalarTower E K A] in
/-- The same transport formula in scalar-extended algebra coordinates. -/
theorem complexCocharacterValue_galois_coordinates (s : ℂ ≃ₐ[ℚ] ℂ)
    (χ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶ D.complexRationalGroupScheme)
    (u : ℂˣ) :
    D.rationalAffinePointsEquiv (CommAlgCat.of ℚ ℂ)
        (D.complexCocharacterValue (D.galoisCocharacter s χ) u) =
      D.toSecondKindInvolution.rationalInvolution.coefficientAut s
        (D.rationalAffinePointsEquiv (CommAlgCat.of ℚ ℂ)
          (D.complexCocharacterValue χ (Units.map s.symm.toMonoidHom u))) := by
  exact (congrArg (D.rationalAffinePointsEquiv (CommAlgCat.of ℚ ℂ))
    (D.complexCocharacterValue_galois s χ u)).trans
      (D.complexPointGaloisAction_coordinates s
        (D.complexCocharacterValue χ (Units.map s.symm.toMonoidHom u)))

omit [IsScalarTower E K A] in
/-- The combined point-evaluation and algebra-coordinate compatibility target. -/
theorem complexCocharacterGaloisEvaluation : D.ComplexCocharacterGaloisEvaluation :=
  fun s χ u => ⟨D.complexCocharacterValue_galois s χ u,
    D.complexCocharacterValue_galois_coordinates s χ u⟩

end Langlands.Shimura.CentralSimpleUnitaryData
