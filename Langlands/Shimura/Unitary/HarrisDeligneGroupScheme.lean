import Langlands.Shimura.Unitary.RealSplitting
import Langlands.Shimura.Unitary.RationalScalarExtension

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Algebra
open scoped CategoryTheory.MonObj TensorProduct Classical

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

/-- The corrected Harris map targets the actual real pullback of the rational CM group. -/
def harrisDeligneMap : DeligneTorus.groupScheme ⟶
    D.rationalBaseChange (AlgebraInvolution.SchemeModel.scalarBaseMap ℚ ℝ) :=
  AlgebraInvolution.SchemeModel.rationalDeligneGroupSchemeMap D.rationalBasis
    D.toSecondKindInvolution.rationalInvolution (D.realComplexHom C)

/-- Recover the map to the scalar-extended coordinate model. -/
theorem harrisDeligneMap_comparison :
    D.harrisDeligneMap C ≫ D.realGroupSchemeIso.hom =
      (D.realComplexHom C).deligneGroupSchemeMap (D.rationalBasis.baseChange ℝ) :=
  AlgebraInvolution.SchemeModel.rationalDeligneGroupSchemeMap_comparison _ _ _

/-- The inverse convention also targets the actual real pullback. -/
def harrisInverseDeligneMap : DeligneTorus.groupScheme ⟶
    D.rationalBaseChange (AlgebraInvolution.SchemeModel.scalarBaseMap ℚ ℝ) :=
  AlgebraInvolution.SchemeModel.rationalInverseDeligneGroupSchemeMap D.rationalBasis
    D.toSecondKindInvolution.rationalInvolution (D.realComplexHom C)

theorem harrisInverseDeligneMap_comparison :
    D.harrisInverseDeligneMap C ≫ D.realGroupSchemeIso.hom =
      (D.realComplexHom C).inverseDeligneGroupSchemeMap (D.rationalBasis.baseChange ℝ) :=
  AlgebraInvolution.SchemeModel.rationalInverseDeligneGroupSchemeMap_comparison _ _ _

/-- The actual algebraic point formula on every affine real test scheme. -/
theorem harrisDeligneMap_affinePoints {S : CommAlgCat ℝ}
    (f : (algSpec (CommRingCat.of ℝ)).obj (op S) ⟶ DeligneTorus.groupScheme.X) :
    (D.toSecondKindInvolution.rationalInvolution.baseChange ℝ).similitudeAffinePointsEquiv
        (D.rationalBasis.baseChange ℝ) S
        (f ≫ (D.harrisDeligneMap C ≫ D.realGroupSchemeIso.hom).hom.hom) =
      (D.realComplexHom C).delignePoints S (DeligneTorus.affinePointsEquiv S f) :=
  AlgebraInvolution.SchemeModel.rationalDeligneGroupSchemeMap_affinePoints _ _ _ f

/-- The inverse convention evaluates at the inverse Deligne point. -/
theorem harrisInverseDeligneMap_affinePoints {S : CommAlgCat ℝ}
    (f : (algSpec (CommRingCat.of ℝ)).obj (op S) ⟶ DeligneTorus.groupScheme.X) :
    (D.toSecondKindInvolution.rationalInvolution.baseChange ℝ).similitudeAffinePointsEquiv
        (D.rationalBasis.baseChange ℝ) S
        (f ≫ (D.harrisInverseDeligneMap C ≫ D.realGroupSchemeIso.hom).hom.hom) =
      (D.realComplexHom C).delignePoints S (DeligneTorus.affinePointsEquiv S f)⁻¹ :=
  AlgebraInvolution.SchemeModel.rationalInverseDeligneGroupSchemeMap_affinePoints _ _ _ f

omit [IsScalarTower ℚ K A] in
/-- At complex scalars the algebraic map has the corrected matrix diagonal. -/
theorem harrisDelignePoints_real_matrix (z : ℂˣ) (τ : E →+* ℝ) :
    D.realMatrixEquiv C
      (Algebra.TensorProduct.lid ℝ (ℝ ⊗[ℚ] A)
        ((((D.realComplexHom C).delignePoints ℝ
          (Units.map (DeligneTorus.complexMap ℝ).toMonoidHom z)).val.1 :
            ℝ ⊗[ℝ] (ℝ ⊗[ℚ] A)))) τ =
      correctedComplexHom n (if τ = C.distinguished then n - 1 else n) (z : ℂ) := by
  change D.realMatrixEquiv C
    (Algebra.TensorProduct.lid ℝ (ℝ ⊗[ℚ] A)
      ((D.realComplexHom C).deligneAlgebraMap ℝ
        (DeligneTorus.complexMap ℝ (z : ℂ)))) τ = _
  rw [(D.realComplexHom C).deligneAlgebraMap_complexMap]
  simp [realMatrixEquiv, realComplexHom]

omit [IsScalarTower ℚ K A] in
/-- The multiplier on the point map is the Deligne norm. -/
theorem harrisDelignePoints_multiplier {S : CommAlgCat ℝ} (z : DeligneTorus.Points S) :
    ((D.toSecondKindInvolution.rationalInvolution.baseChange ℝ).baseChange S).multiplier
      ((D.realComplexHom C).delignePoints S z) = DeligneTorus.norm S z := rfl

/-- Actual real scheme points, identified with complex units, have the corrected matrix formula. -/
theorem harrisDeligneMap_real_matrix (z : ℂˣ) (τ : E →+* ℝ) :
    let f := (DeligneTorus.affinePointsEquiv (CommAlgCat.of ℝ ℝ)).symm
      (Units.map (DeligneTorus.complexMap ℝ).toMonoidHom z)
    let g := (D.toSecondKindInvolution.rationalInvolution.baseChange ℝ).similitudeAffinePointsEquiv
      (D.rationalBasis.baseChange ℝ) (CommAlgCat.of ℝ ℝ)
      (f ≫ (D.harrisDeligneMap C ≫ D.realGroupSchemeIso.hom).hom.hom)
    D.realMatrixEquiv C
      (Algebra.TensorProduct.lid ℝ (ℝ ⊗[ℚ] A)
        (g.val.1 : ℝ ⊗[ℝ] (ℝ ⊗[ℚ] A))) τ =
      correctedComplexHom n (if τ = C.distinguished then n - 1 else n) (z : ℂ) := by
  dsimp only
  rw [D.harrisDeligneMap_affinePoints C, MulEquiv.apply_symm_apply]
  exact D.harrisDelignePoints_real_matrix C z τ

/-- Kottwitz's inverse-of-h₀ convention uses the conjugate of the constructed Harris map. -/
def kottwitzDeligneMap : DeligneTorus.groupScheme ⟶
    D.rationalBaseChange (AlgebraInvolution.SchemeModel.scalarBaseMap ℚ ℝ) :=
  AlgebraInvolution.SchemeModel.rationalInverseDeligneGroupSchemeMap D.rationalBasis
    D.toSecondKindInvolution.rationalInvolution (D.realComplexHom C).conj

/-- The Kottwitz convention recovers the inverse map of the conjugate complex homomorphism. -/
theorem kottwitzDeligneMap_comparison :
    D.kottwitzDeligneMap C ≫ D.realGroupSchemeIso.hom =
      (D.realComplexHom C).conj.inverseDeligneGroupSchemeMap (D.rationalBasis.baseChange ℝ) :=
  AlgebraInvolution.SchemeModel.rationalInverseDeligneGroupSchemeMap_comparison _ _ _

/-- The Kottwitz convention on affine points retains both conjugation and inversion. -/
theorem kottwitzDeligneMap_affinePoints {S : CommAlgCat ℝ}
    (f : (algSpec (CommRingCat.of ℝ)).obj (op S) ⟶ DeligneTorus.groupScheme.X) :
    (D.toSecondKindInvolution.rationalInvolution.baseChange ℝ).similitudeAffinePointsEquiv
        (D.rationalBasis.baseChange ℝ) S
        (f ≫ (D.kottwitzDeligneMap C ≫ D.realGroupSchemeIso.hom).hom.hom) =
      (D.realComplexHom C).conj.delignePoints S (DeligneTorus.affinePointsEquiv S f)⁻¹ :=
  AlgebraInvolution.SchemeModel.rationalInverseDeligneGroupSchemeMap_affinePoints _ _ _ f

/-- Construct the actual Harris group-scheme homomorphism directly from the signature hypotheses. -/
def harrisDeligneMapOfSignature (h : HasHarrisSignature D.toSecondKindInvolution n)
    (hΦ : IsCMSection E K Φ) : DeligneTorus.groupScheme ⟶
      D.rationalBaseChange (AlgebraInvolution.SchemeModel.scalarBaseMap ℚ ℝ) :=
  D.harrisDeligneMap (HarrisSignatureCharts.ofSignature h hΦ)

end Langlands.Shimura.CentralSimpleUnitaryData
