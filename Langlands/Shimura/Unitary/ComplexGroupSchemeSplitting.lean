import Langlands.Shimura.Unitary.ComplexGroupPoints
import Langlands.GroupScheme.GeneralLinearProduct

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Algebra Module
open scoped CategoryTheory.MonObj Classical

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

/-- The explicit split complex group scheme for the Harris group. -/
abbrev complexSplitGroupScheme (_D : CentralSimpleUnitaryData E K A n) : GroupScheme (Spec (CommRingCat.of ℂ)) :=
  GroupScheme.GeneralLinearProduct.groupScheme n (E →+* ℝ) (CommRingCat.of ℂ)

/-- The natural comparison of actual Harris points and actual product-scheme points. -/
def complexSplitPointsEquiv (T : Over (Spec (CommRingCat.of ℂ))) :
    (T ⟶ D.complexRationalGroupScheme.X) ≃* (T ⟶ D.complexSplitGroupScheme.X) :=
  (D.complexGroupPointsEquiv C T).trans
    (GroupScheme.GeneralLinearProduct.pointsEquiv n (E →+* ℝ) (CommRingCat.of ℂ) T).symm

/-- The point comparison preserves the established matrix and scalar coordinates. -/
theorem complexSplitPointsEquiv_coordinates (T : Over (Spec (CommRingCat.of ℂ)))
    (x : T ⟶ D.complexRationalGroupScheme.X) :
    GroupScheme.GeneralLinearProduct.pointsEquiv n (E →+* ℝ) (CommRingCat.of ℂ) T
      (D.complexSplitPointsEquiv C T x) = D.complexGroupPointsEquiv C T x :=
  MulEquiv.apply_symm_apply _ _

/-- The comparison commutes with every complex test-scheme morphism. -/
theorem complexSplitPointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of ℂ))}
    (a : T' ⟶ T) (x : T ⟶ D.complexRationalGroupScheme.X) :
    D.complexSplitPointsEquiv C T' (a ≫ x) = a ≫ D.complexSplitPointsEquiv C T x := by
  apply (GroupScheme.GeneralLinearProduct.pointsEquiv n (E →+* ℝ)
    (CommRingCat.of ℂ) T').injective
  exact (D.complexSplitPointsEquiv_coordinates C T' (a ≫ x)).trans
    ((D.complexGroupPointsEquiv_naturality C a x).trans
      ((congrArg (ComplexMatrix.splitGroupMap n (E →+* ℝ) a.left.appTop.hom)
        (D.complexSplitPointsEquiv_coordinates C T x).symm).trans
          (GroupScheme.GeneralLinearProduct.pointsEquiv_naturality n (E →+* ℝ)
            (CommRingCat.of ℂ) a (D.complexSplitPointsEquiv C T x)).symm))

/-- The actual complex Harris group is the finite product of GL_n with one Gm. -/
def complexGroupSchemeIso : D.complexRationalGroupScheme ≅ D.complexSplitGroupScheme :=
  GroupScheme.isoOfPoints (D.complexSplitPointsEquiv C)
    (D.complexSplitPointsEquiv_naturality C)

/-- The scheme isomorphism realizes precisely the established Harris matrix coordinates. -/
theorem complexGroupSchemeIso_hom_points (T : Over (Spec (CommRingCat.of ℂ)))
    (x : T ⟶ D.complexRationalGroupScheme.X) :
    GroupScheme.GeneralLinearProduct.pointsEquiv n (E →+* ℝ) (CommRingCat.of ℂ) T
      (x ≫ (D.complexGroupSchemeIso C).hom.hom.hom) = D.complexGroupPointsEquiv C T x := by
  have h : x ≫ (D.complexGroupSchemeIso C).hom.hom.hom =
      D.complexSplitPointsEquiv C T x :=
    GroupScheme.comp_isoOfPoints_hom _ (D.complexSplitPointsEquiv_naturality C) T x
  rw [h]
  exact MulEquiv.apply_symm_apply _ _

/-- The inverse scheme morphism recovers the prescribed matrices and common multiplier. -/
theorem complexGroupSchemeIso_inv_points (T : Over (Spec (CommRingCat.of ℂ)))
    (y : T ⟶ D.complexSplitGroupScheme.X) :
    D.complexGroupPointsEquiv C T (y ≫ (D.complexGroupSchemeIso C).inv.hom.hom) =
      GroupScheme.GeneralLinearProduct.pointsEquiv n (E →+* ℝ) (CommRingCat.of ℂ) T y := by
  have h : y ≫ (D.complexGroupSchemeIso C).inv.hom.hom =
      (D.complexSplitPointsEquiv C T).symm y :=
    GroupScheme.comp_isoOfPoints_inv _ (D.complexSplitPointsEquiv_naturality C) T y
  rw [h]
  exact MulEquiv.apply_symm_apply _ _

end Langlands.Shimura.CentralSimpleUnitaryData
