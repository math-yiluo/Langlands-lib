import Langlands.Global.RealAlgebraSplitting
import Langlands.Shimura.Unitary.HarrisLevels
import Langlands.Shimura.Unitary.InvolutionBaseChangeTower

noncomputable section
universe u v w z
open NumberField Module Algebra
open scoped TensorProduct Classical

namespace Langlands.Shimura.HarrisSignatureCharts

variable {E : Type u} {K : Type v} {A : Type w}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K]
  [Ring A] [Algebra E A] [Algebra K A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {σ : SecondKindInvolution E K A} {n : ℕ}
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts σ n Φ)
  {ι : Type z} [Fintype ι] (b : Basis ι E A)

/-- Assemble the actual real-place charts into an isomorphism from the rational real tensor. -/
def realMatrixEquiv : ℝ ⊗[ℚ] A ≃ₐ[ℝ] ((E →+* ℝ) → Matrix (Fin n) (Fin n) ℂ) :=
  (Global.TotallyReal.algebraEquiv E A b).trans (AlgEquiv.piCongrRight C.equiv)

@[simp] theorem realMatrixEquiv_tmul (r : ℝ) (a : A) (τ : E →+* ℝ) :
    letI : Algebra E ℝ := τ.toAlgebra
    C.realMatrixEquiv b (r ⊗ₜ[ℚ] a) τ = C.equiv τ (r ⊗ₜ[E] a) := by
  simp [realMatrixEquiv]

/-- On rationally embedded elements the real isomorphism recovers the existing chart evaluation. -/
@[simp] theorem realMatrixEquiv_one_tmul (a : A) :
    C.realMatrixEquiv b ((1 : ℝ) ⊗ₜ[ℚ] a) = C.evaluation a := by
  funext τ
  exact C.realMatrixEquiv_tmul b 1 a τ

/-- The assembled isomorphism identifies the actual scalar-extended involution with the signatures. -/
theorem realMatrixEquiv_involution (x : ℝ ⊗[ℚ] A) :
    C.realMatrixEquiv b (σ.rationalInvolution.baseChange ℝ x) =
      harrisArchimedeanInvolution n (E →+* ℝ) C.distinguished (C.realMatrixEquiv b x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    funext τ
    let : Algebra E ℝ := τ.toAlgebra
    simpa [harrisArchimedeanInvolution, AlgebraInvolution.pi] using
      C.compatible τ (r ⊗ₜ[E] a)
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The real similitude groups agree through the actual algebra isomorphism. -/
def realSimilitudesEquiv :
    (σ.rationalInvolution.baseChange ℝ).similitudes ≃*
      (harrisArchimedeanInvolution n (E →+* ℝ) C.distinguished).similitudes :=
  AlgebraInvolution.similitudesEquiv _ _ (C.realMatrixEquiv b)
    (C.realMatrixEquiv_involution b)

@[simp] theorem realSimilitudesEquiv_multiplier
    (g : (σ.rationalInvolution.baseChange ℝ).similitudes) :
    (harrisArchimedeanInvolution n (E →+* ℝ) C.distinguished).multiplier
      (C.realSimilitudesEquiv b g) =
      (σ.rationalInvolution.baseChange ℝ).multiplier g :=
  AlgebraInvolution.similitudesEquiv_multiplier _ _ _ _ g

/-- The earlier chart action of rational points is the actual diagonal real action. -/
theorem realSimilitudesEquiv_diagonal :
    (C.realSimilitudesEquiv b).toMonoidHom.comp (σ.rationalInvolution.diagonalPoints ℝ) =
      C.rationalMap := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    exact C.realMatrixEquiv_one_tmul b (g.val.1 : A)
  · exact Units.ext rfl

/-- The corrected complex homomorphism in the actual real scalar extension of the original algebra. -/
def realComplexHom : AlgebraInvolution.ComplexHom (σ.rationalInvolution.baseChange ℝ) where
  hom := (C.realMatrixEquiv b).symm.toAlgHom.comp
    (harrisArchimedeanHom n (E →+* ℝ) C.distinguished).hom
  star_compatible z := by
    apply (C.realMatrixEquiv b).injective
    rw [C.realMatrixEquiv_involution b]
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
    exact (harrisArchimedeanHom n (E →+* ℝ) C.distinguished).star_compatible z

/-- In matrix coordinates the constructed homomorphism has the corrected Harris diagonal formula. -/
@[simp] theorem realComplexHom_matrix (z : ℂ) (τ : E →+* ℝ) :
    C.realMatrixEquiv b ((C.realComplexHom b).hom z) τ =
      correctedComplexHom n (if τ = C.distinguished then n - 1 else n) z := by
  change C.realMatrixEquiv b
    ((C.realMatrixEquiv b).symm ((harrisArchimedeanHom n _ C.distinguished).hom z)) τ = _
  rw [AlgEquiv.apply_symm_apply]
  rfl

theorem realComplexHom_similitudes :
    (C.realSimilitudesEquiv b).toMonoidHom.comp (C.realComplexHom b).toSimilitudes =
      (harrisArchimedeanHom n (E →+* ℝ) C.distinguished).toSimilitudes := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    funext τ
    exact C.realComplexHom_matrix b (g : ℂ) τ
  · exact Units.ext rfl

end Langlands.Shimura.HarrisSignatureCharts

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E : Type u} {K : Type v} {A : Type w}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K]
  [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)

/-- The finite basis over the totally real field follows from the actual finite CM algebra. -/
def totallyRealBasis : Basis (Fin (Module.finrank E A)) E A := by
  letI : FiniteDimensional E K :=
    Module.finite_of_finrank_eq_succ (IsQuadraticExtension.finrank_eq_two E K)
  letI : FiniteDimensional K A := D.finite
  letI : FiniteDimensional E A := FiniteDimensional.trans E K A
  exact Module.finBasis E A

variable [Algebra ℚ A] [IsScalarTower ℚ E A]
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

/-- The real matrix splitting for the actual central simple CM algebra. -/
def realMatrixEquiv : ℝ ⊗[ℚ] A ≃ₐ[ℝ] ((E →+* ℝ) → Matrix (Fin n) (Fin n) ℂ) :=
  C.realMatrixEquiv D.totallyRealBasis

/-- The complex homomorphism into the actual real CM algebra, constructed from its charts. -/
def realComplexHom :
    AlgebraInvolution.ComplexHom (D.toSecondKindInvolution.rationalInvolution.baseChange ℝ) :=
  C.realComplexHom D.totallyRealBasis

/-- Signature and CM-section hypotheses supply the charts used in the construction. -/
def realComplexHomOfSignature (h : HasHarrisSignature D.toSecondKindInvolution n)
    (hΦ : IsCMSection E K Φ) :
    AlgebraInvolution.ComplexHom (D.toSecondKindInvolution.rationalInvolution.baseChange ℝ) :=
  D.realComplexHom (HarrisSignatureCharts.ofSignature h hΦ)

end Langlands.Shimura.CentralSimpleUnitaryData
