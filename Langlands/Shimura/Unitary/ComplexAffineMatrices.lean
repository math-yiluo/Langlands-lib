import Langlands.Shimura.Unitary.ComplexAffineCoordinates
import Langlands.Shimura.Unitary.ComplexCocharacterMatrices
import Langlands.Shimura.Unitary.GaloisPointMatrices

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Algebra Module
open scoped CategoryTheory.MonObj TensorProduct Classical
attribute [local instance 1100] Algebra.toModule

namespace Langlands.Shimura.HarrisSignatureCharts

variable {E K A : Type*}
  [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K]
  [Ring A] [Algebra E A] [Algebra K A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {σ : SecondKindInvolution E K A} {n : ℕ}
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts σ n Φ)
  {κ : Type*} [Fintype κ] (b : Basis κ E A)
  {S T : Type*} [CommRing S] [CommRing T]
  [Algebra ℂ S] [Algebra ℝ S] [IsScalarTower ℝ ℂ S]
  [Algebra ℂ T] [Algebra ℝ T] [IsScalarTower ℝ ℂ T]

/-- The full Harris matrix decomposition commutes with complex coefficient change. -/
theorem iteratedScalarMatrixEquiv_natural_apply (f : S →ₐ[ℂ] T)
    (x : S ⊗[ℝ] (ℝ ⊗[ℚ] A)) (τ : E →+* ℝ) :
    C.iteratedScalarMatrixEquiv b T
        (AlgebraInvolution.changeCoefficients (f.restrictScalars ℝ) x) τ =
      ((C.iteratedScalarMatrixEquiv b S x τ).1.map f,
        (C.iteratedScalarMatrixEquiv b S x τ).2.map f) := by
  induction x using TensorProduct.inductionOn with
  | tmul s a =>
    apply Prod.ext <;> ext i j <;>
      simp [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, AlgHom.commutes]
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, hx, hy]
    apply Prod.ext <;> ext i j <;> simp [Matrix.map_apply]

/-- At complex coefficients the two published matrix splittings agree. -/
theorem iteratedScalarMatrixEquiv_complex (x : ℂ ⊗[ℝ] (ℝ ⊗[ℚ] A)) :
    C.iteratedScalarMatrixEquiv b ℂ x = C.iteratedComplexMatrixEquiv b x := by
  induction x using TensorProduct.inductionOn with
  | tmul z a =>
    funext τ
    apply Prod.ext <;> ext i j <;>
      simp [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

end Langlands.Shimura.HarrisSignatureCharts

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
  (T : Type) [CommRing T] [Algebra ℂ T] [Algebra ℝ T] [Algebra ℚ T]
  [IsScalarTower ℝ ℂ T] [IsScalarTower ℚ ℝ T]

/-- Matrix coordinates of an affine complex Harris point, in its actual coefficient algebra. -/
def complexAffinePointMatrices
    (x : (algSpec (CommRingCat.of ℂ)).obj (op (CommAlgCat.of ℂ T)) ⟶
      D.complexRationalGroupScheme.X) :
    (E →+* ℝ) → Matrix (Fin n) (Fin n) T × Matrix (Fin n) (Fin n) T :=
  C.iteratedScalarMatrixEquiv D.totallyRealBasis T
    ((D.complexAffineSimilitudes T x).val.1 : T ⊗[ℝ] (ℝ ⊗[ℚ] A))

/-- Affine matrices agree with the direct rational tensor splitting of the projected point. -/
theorem complexAffinePointMatrices_rational
    (x : (algSpec (CommRingCat.of ℂ)).obj (op (CommAlgCat.of ℂ T)) ⟶
      D.complexRationalGroupScheme.X) :
    D.complexAffinePointMatrices C T x =
      C.scalarMatrixEquiv D.totallyRealBasis T
        ((D.rationalAffinePointsEquiv (CommAlgCat.of ℚ T)
          (D.complexAffineRationalPoint T x)).val.1 : T ⊗[ℚ] A) := by
  rw [complexAffinePointMatrices, D.complexAffineSimilitudes_tower]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [Algebra ℚ T] [IsScalarTower ℚ ℝ T] in
/-- Normalizing the global-section matrices of an affine test gives its affine matrices. -/
theorem complexAffinePointMatrices_sections
    (x : (algSpec (CommRingCat.of ℂ)).obj (op (CommAlgCat.of ℂ T)) ⟶
      D.complexRationalGroupScheme.X) (τ : E →+* ℝ) :
    D.complexAffinePointMatrices C T x τ =
      ((D.complexPointMatrices C
          ((algSpec (CommRingCat.of ℂ)).obj (op (CommAlgCat.of ℂ T))) x τ).1.map
          (GroupScheme.Corepresented.affineSectionsAlgEquiv (R := CommRingCat.of ℂ)
            (CommAlgCat.of ℂ T)),
       (D.complexPointMatrices C
          ((algSpec (CommRingCat.of ℂ)).obj (op (CommAlgCat.of ℂ T))) x τ).2.map
          (GroupScheme.Corepresented.affineSectionsAlgEquiv (R := CommRingCat.of ℂ)
            (CommAlgCat.of ℂ T))) := by
  exact C.iteratedScalarMatrixEquiv_natural_apply D.totallyRealBasis
    (S := AlgebraInvolution.complexTestAlgebra
      ((algSpec (CommRingCat.of ℂ)).obj (op (CommAlgCat.of ℂ T)))) (T := T)
    (GroupScheme.Corepresented.affineSectionsAlgEquiv (R := CommRingCat.of ℂ)
      (CommAlgCat.of ℂ T)).toAlgHom
    ((AlgebraInvolution.complexSimilitudePointsEquiv (D.rationalBasis.baseChange ℝ)
      (D.toSecondKindInvolution.rationalInvolution.baseChange ℝ) _
        (x ≫ ((Over.pullback DeligneTorus.complexBaseMap).mapGrp.map
          D.realGroupSchemeIso.hom).hom.hom)).val.1 :
      AlgebraInvolution.complexTestAlgebra
        ((algSpec (CommRingCat.of ℂ)).obj (op (CommAlgCat.of ℂ T))) ⊗[ℝ] (ℝ ⊗[ℚ] A)) τ

variable {T}

/-- Each embedding-labelled rational matrix is the corresponding normalized affine matrix factor. -/
theorem complexEmbeddingPointMatrices_affine (hΦ : IsCMSection E K Φ)
    (x : (algSpec (CommRingCat.of ℂ)).obj (op (CommAlgCat.of ℂ ℂ)) ⟶
      D.complexRationalGroupScheme.X) (p : (E →+* ℝ) × Bool) :
    D.complexEmbeddingPointMatrices C hΦ (D.complexAffineRationalPoint ℂ x)
        (cmFactorEmbedding Φ p) =
      if p.2 then (D.complexAffinePointMatrices C ℂ x p.1).1
      else (D.complexAffinePointMatrices C ℂ x p.1).2 := by
  change C.embeddingMatrixEquiv hΦ D.totallyRealBasis
    ((D.rationalAffinePointsEquiv (CommAlgCat.of ℚ ℂ)
      (D.complexAffineRationalPoint ℂ x)).val.1 : ℂ ⊗[ℚ] A)
        (cmFactorEmbedding Φ p) = _
  rw [C.embeddingMatrixEquiv_factor, D.complexAffinePointMatrices_rational]
  simp only [HarrisSignatureCharts.scalarMatrixEquiv, HarrisSignatureCharts.complexMatrixEquiv,
    AlgEquiv.trans_apply, C.iteratedScalarMatrixEquiv_complex]

end Langlands.Shimura.CentralSimpleUnitaryData
