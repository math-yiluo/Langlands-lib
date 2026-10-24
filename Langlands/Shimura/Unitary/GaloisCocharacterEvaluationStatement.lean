import Langlands.Shimura.Unitary.GaloisCocharacterPoints

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Algebra
open scoped CategoryTheory.MonObj

namespace Langlands.Shimura.CentralSimpleUnitaryData
variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)

/-- Galois evaluation on actual complex points and on algebra coordinates. -/
def ComplexCocharacterGaloisEvaluation : Prop :=
  ∀ (s : ℂ ≃ₐ[ℚ] ℂ)
    (χ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶ D.complexRationalGroupScheme)
    (u : ℂˣ),
    (D.complexCocharacterValue (D.galoisCocharacter s χ) u =
      D.complexPointGaloisAction s
        (D.complexCocharacterValue χ (Units.map s.symm.toMonoidHom u))) ∧
    (D.rationalAffinePointsEquiv (CommAlgCat.of ℚ ℂ)
        (D.complexCocharacterValue (D.galoisCocharacter s χ) u) =
      D.toSecondKindInvolution.rationalInvolution.coefficientAut s
        (D.rationalAffinePointsEquiv (CommAlgCat.of ℚ ℂ)
          (D.complexCocharacterValue χ (Units.map s.symm.toMonoidHom u))))

end Langlands.Shimura.CentralSimpleUnitaryData
