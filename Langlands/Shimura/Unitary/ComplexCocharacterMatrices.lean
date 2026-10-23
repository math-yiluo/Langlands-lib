import Langlands.Shimura.Unitary.ComplexMatrixWeights

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Algebra Module
open scoped CategoryTheory.MonObj TensorProduct Classical
attribute [local instance 1100] Algebra.toModule

namespace Langlands.Shimura.AlgebraInvolution

/-- Complex scalars on test-scheme sections come from the complex structure morphism. -/
instance complexTestAlgebraComplex (T : Over (Spec (CommRingCat.of ℂ))) :
    Algebra ℂ (complexTestAlgebra T) :=
  ((algΓ (CommRingCat.of ℂ)).obj T).unop.algebra

/-- The real and complex structure maps on global sections form the actual scalar tower. -/
instance complexTestAlgebraTower (T : Over (Spec (CommRingCat.of ℂ))) :
    IsScalarTower ℝ ℂ (complexTestAlgebra T) := by
  apply IsScalarTower.of_algebraMap_eq'
  change ((Scheme.ΓSpecIso (CommRingCat.of ℝ)).inv ≫
      (T.hom ≫ DeligneTorus.complexBaseMap).appTop).hom =
    ((CommRingCat.ofHom (algebraMap ℝ ℂ)) ≫
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ T.hom.appTop).hom
  congr 1
  rw [Scheme.Hom.comp_appTop]
  rw [← Category.assoc, DeligneTorus.complexBaseMap,
    ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]

end Langlands.Shimura.AlgebraInvolution

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

/-- Matrix coordinates of points of the actual complex pullback of the rational Harris group. -/
def complexPointMatrices (T : Over (Spec (CommRingCat.of ℂ)))
    (g : T ⟶ D.complexRationalGroupScheme.X) :
    (E →+* ℝ) → Matrix (Fin n) (Fin n) (AlgebraInvolution.complexTestAlgebra T) ×
      Matrix (Fin n) (Fin n) (AlgebraInvolution.complexTestAlgebra T) :=
  C.iteratedScalarMatrixEquiv D.totallyRealBasis (AlgebraInvolution.complexTestAlgebra T)
    ((AlgebraInvolution.complexSimilitudePointsEquiv (D.rationalBasis.baseChange ℝ)
      (D.toSecondKindInvolution.rationalInvolution.baseChange ℝ) T
        (g ≫ ((Over.pullback DeligneTorus.complexBaseMap).mapGrp.map
          D.realGroupSchemeIso.hom).hom.hom)).val.1 :
        (AlgebraInvolution.complexTestAlgebra T) ⊗[ℝ] (ℝ ⊗[ℚ] A))

/-- On every complex test scheme, the actual Harris cocharacter has the corrected diagonal weights. -/
theorem harrisCocharacter_matrices (first : Bool) (T : Over (Spec (CommRingCat.of ℂ)))
    (x : T ⟶ (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).X) (τ : E →+* ℝ) :
    D.complexPointMatrices C T (x ≫ (D.harrisCocharacter C first).hom.hom) τ =
      ComplexMatrix.splitDiagonal (AlgebraInvolution.complexTestAlgebra T) n
        (if τ = C.distinguished then n - 1 else n)
        (if first then ((GroupScheme.Gm.pointsEquiv _ T x : Γ(T.left, ⊤)), 1)
          else (1, (GroupScheme.Gm.pointsEquiv _ T x : Γ(T.left, ⊤)))) := by
  unfold complexPointMatrices
  rw [Category.assoc, ← Grp.comp_hom_hom, D.harrisCocharacter_comparison,
    AlgebraInvolution.ComplexHom.cocharacter_points, DeligneTorus.factorCocharacter_quadratic]
  cases first
  · exact C.delignePoints_secondFactor D.totallyRealBasis _ _ τ
  · exact C.delignePoints_firstFactor D.totallyRealBasis _ _ τ

end Langlands.Shimura.CentralSimpleUnitaryData
