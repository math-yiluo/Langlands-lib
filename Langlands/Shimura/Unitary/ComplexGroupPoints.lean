import Langlands.Shimura.Unitary.ComplexGroupNaturality
import Langlands.Shimura.Unitary.ComplexCocharacterMatrices

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Algebra Module
open scoped CategoryTheory.MonObj TensorProduct Classical
attribute [local instance 1100] Algebra.toModule

namespace Langlands.Shimura.AlgebraInvolution

/-- The actual complex algebra map on sections induced by a test-scheme morphism. -/
def complexTestAlgebraMap {T T' : Over (Spec (CommRingCat.of ℂ))} (a : T' ⟶ T) :
    complexTestAlgebra T →ₐ[ℂ] complexTestAlgebra T' :=
  ((algΓ (CommRingCat.of ℂ)).map a).unop.hom

variable {A : Type} [Ring A] [Algebra ℝ A]
  {κ : Type} [Fintype κ] (b : Module.Basis κ ℝ A) (σ : AlgebraInvolution ℝ A)

/-- Restriction of actual complex pullback points is the corresponding tensor coefficient map. -/
theorem complexSimilitudePointsEquiv_naturality
    {T T' : Over (Spec (CommRingCat.of ℂ))} (a : T' ⟶ T)
    (x : T ⟶ ((Over.pullback DeligneTorus.complexBaseMap).mapGrp.obj
      (σ.similitudeGroupScheme b)).X) :
    complexSimilitudePointsEquiv b σ T' (a ≫ x) =
      σ.baseChangeMap (CommAlgCat.ofHom ((complexTestAlgebraMap a).restrictScalars ℝ))
        (complexSimilitudePointsEquiv b σ T x) := by
  change GroupScheme.Corepresented.pointsEquiv (R := CommRingCat.of ℝ)
    σ.similitudeFunctor (σ.similitudeCorepresentableBy b) _
      (GroupScheme.baseChangePointsEquiv _ _ _ (a ≫ x)) = _
  rw [GroupScheme.baseChangePointsEquiv_naturality,
    GroupScheme.Corepresented.pointsEquiv_naturality]
  rfl

end Langlands.Shimura.AlgebraInvolution

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

/-- Split points of the actual complex Harris group on every test scheme. -/
def complexGroupPointsEquiv (T : Over (Spec (CommRingCat.of ℂ))) :
    (T ⟶ D.complexRationalGroupScheme.X) ≃*
      (((E →+* ℝ) → (Matrix (Fin n) (Fin n) (AlgebraInvolution.complexTestAlgebra T))ˣ) ×
        (AlgebraInvolution.complexTestAlgebra T)ˣ) :=
  (((yonedaGrp.mapIso ((Over.pullback DeligneTorus.complexBaseMap).mapGrp.mapIso
    D.realGroupSchemeIso)).app (op T)).groupIsoToMulEquiv).trans
      ((AlgebraInvolution.complexSimilitudePointsEquiv (D.rationalBasis.baseChange ℝ)
        (D.toSecondKindInvolution.rationalInvolution.baseChange ℝ) T).trans
          (C.iteratedScalarGroupSplitting D.totallyRealBasis
            (AlgebraInvolution.complexTestAlgebra T)))

/-- The matrix component agrees with the previously computed cocharacter coordinates. -/
@[simp] theorem complexGroupPointsEquiv_matrix (T : Over (Spec (CommRingCat.of ℂ)))
    (g : T ⟶ D.complexRationalGroupScheme.X) (τ : E →+* ℝ) :
    ((D.complexGroupPointsEquiv C T g).1 τ :
      Matrix (Fin n) (Fin n) (AlgebraInvolution.complexTestAlgebra T)) =
      (D.complexPointMatrices C T g τ).1 := rfl

/-- The scalar factor is exactly the multiplier in the actual scalar-extended algebra. -/
@[simp] theorem complexGroupPointsEquiv_multiplier (T : Over (Spec (CommRingCat.of ℂ)))
    (g : T ⟶ D.complexRationalGroupScheme.X) :
    (D.complexGroupPointsEquiv C T g).2 =
      ((D.toSecondKindInvolution.rationalInvolution.baseChange ℝ).baseChange
        (AlgebraInvolution.complexTestAlgebra T)).multiplier
          (AlgebraInvolution.complexSimilitudePointsEquiv (D.rationalBasis.baseChange ℝ)
            (D.toSecondKindInvolution.rationalInvolution.baseChange ℝ) T
              (g ≫ ((Over.pullback DeligneTorus.complexBaseMap).mapGrp.map
                D.realGroupSchemeIso.hom).hom.hom)) := by
  exact Units.ext rfl

/-- The second matrix is determined by the first matrix and the common scalar multiplier. -/
theorem complexGroupPointsEquiv_second (T : Over (Spec (CommRingCat.of ℂ)))
    (g : T ⟶ D.complexRationalGroupScheme.X) (τ : E →+* ℝ) :
    (D.complexPointMatrices C T g τ).2 =
      algebraMap (AlgebraInvolution.complexTestAlgebra T)
        (Matrix (Fin n) (Fin n) (AlgebraInvolution.complexTestAlgebra T))
          ((D.complexGroupPointsEquiv C T g).2 : AlgebraInvolution.complexTestAlgebra T) *
        ComplexMatrix.signatureTransposeOver (AlgebraInvolution.complexTestAlgebra T) n
          (if τ = C.distinguished then n - 1 else n)
            (((D.complexGroupPointsEquiv C T g).1 τ)⁻¹ :
              (Matrix (Fin n) (Fin n) (AlgebraInvolution.complexTestAlgebra T))ˣ) := by
  let q := AlgebraInvolution.complexSimilitudePointsEquiv (D.rationalBasis.baseChange ℝ)
    (D.toSecondKindInvolution.rationalInvolution.baseChange ℝ) T
      (g ≫ ((Over.pullback DeligneTorus.complexBaseMap).mapGrp.map
        D.realGroupSchemeIso.hom).hom.hom)
  have h := ComplexMatrix.harrisSimilitudesEquiv_symm_second
    (AlgebraInvolution.complexTestAlgebra T) n (E →+* ℝ) C.distinguished
      (C.iteratedScalarGroupSplitting D.totallyRealBasis _ q) τ
  simp only [HarrisSignatureCharts.iteratedScalarGroupSplitting, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] at h
  exact h

/-- Restriction of Harris points is entrywise restriction of matrices and of the scalar unit. -/
theorem complexGroupPointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of ℂ))}
    (a : T' ⟶ T) (g : T ⟶ D.complexRationalGroupScheme.X) :
    D.complexGroupPointsEquiv C T' (a ≫ g) =
      ComplexMatrix.splitGroupMap n (E →+* ℝ) a.left.appTop.hom
        (D.complexGroupPointsEquiv C T g) := by
  change C.iteratedScalarGroupSplitting D.totallyRealBasis _
    (AlgebraInvolution.complexSimilitudePointsEquiv _ _ T' ((a ≫ g) ≫ _)) = _
  rw [Category.assoc, AlgebraInvolution.complexSimilitudePointsEquiv_naturality,
    HarrisSignatureCharts.iteratedScalarGroupSplitting_natural]
  rfl

/-- The full group-valued point presheaf of the actual complex Harris group is split. -/
def complexGroupPointsIso :
    GroupScheme.points D.complexRationalGroupScheme ≅
      GroupScheme.Corepresented.globalPointsFunctor
        (ComplexMatrix.splitGroupFunctor n (E →+* ℝ)) :=
  NatIso.ofComponents (fun T => (D.complexGroupPointsEquiv C T.unop).toGrpIso) (by
    intro T T' a
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    exact D.complexGroupPointsEquiv_naturality C a.unop g)

end Langlands.Shimura.CentralSimpleUnitaryData
