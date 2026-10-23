import Langlands.Shimura.Unitary.RealPositivity
import Langlands.Shimura.Unitary.Reflex
import Langlands.Shimura.Unitary.ReflexGaloisProof

noncomputable section
universe u v w z t
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

/-- In actual matrix coordinates the constructed positive homomorphism is Kottwitz's model. -/
theorem realPositiveKottwitzHom_matrix :
    (C.realMatrixEquiv b).toAlgHom.comp (C.realPositiveKottwitzHom b).val.hom =
      (kottwitzHom n (E →+* ℝ) C.distinguished).hom := by
  apply AlgHom.ext
  intro z
  funext τ
  exact C.realComplexHom_matrix b (star z) τ

/-- The Hodge function of the actual positive homomorphism, computed in its splitting charts. -/
def realHodgeFunction : (K →+* ℂ) → ℕ :=
  standardHodgeFunction Φ
    ((C.realMatrixEquiv b).toAlgHom.comp (C.realPositiveKottwitzHom b).val.hom)

/-- The actual positive homomorphism realizes the previously calculated Hodge function. -/
theorem realHodgeFunction_eq : C.realHodgeFunction b = C.hodgeFunction := by
  rw [realHodgeFunction, C.realPositiveKottwitzHom_matrix]
  rfl

/-- The reflex field attached to the constructed positive homomorphism. -/
def realReflexField : IntermediateField ℚ ℂ :=
  Shimura.reflexField (C.realHodgeFunction b)

theorem realReflexField_eq : C.realReflexField b = C.reflexField := by
  rw [realReflexField, C.realHodgeFunction_eq]
  rfl

theorem realHodgeFunction_apply (hΦ : IsCMSection E K Φ) (i : K →+* ℂ) :
    C.realHodgeFunction b i =
      if i = C.distinguishedEmbedding then n - 1
      else if i = ComplexEmbedding.conjugate C.distinguishedEmbedding then 1
      else if i = Φ (realPlaceBelow E i) then n else 0 := by
  rw [C.realHodgeFunction_eq]
  exact C.hodgeFunction_eq hΦ i

/-- The exceptional rank-two, single-real-place Hodge function has rational reflex field. -/
theorem realReflexField_eq_bot (h2 : n = 2) [Subsingleton (E →+* ℝ)] :
    C.realReflexField b = ⊥ := by
  rw [realReflexField, C.realHodgeFunction_eq, Shimura.reflexField,
    C.hodgeStabilizer_eq_top h2]
  simpa using (complexFixedField (⊥ : IntermediateField ℚ ℂ))

variable {F : Type t} [Field F] [NumberField F] [IsCMField F] [IsQuadraticExtension ℚ F]
  {j : F →+* K} {τ₀ : F →+* ℂ}
  (CH : HarrisSignatureCharts σ n (harrisCMSection E j τ₀))

/-- Away from the exceptional rank-two case, the actual Harris reflex field is the CM image. -/
theorem realReflexField_eq_distinguishedImage
    (h : 3 ≤ n ∨ ∃ τ, τ ≠ CH.distinguished) :
    CH.realReflexField b = CH.distinguishedImage := by
  rw [CH.realReflexField_eq]
  exact CH.reflexField_eq_distinguishedImage h (complexFixedField _)

end Langlands.Shimura.HarrisSignatureCharts

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E : Type u} {K : Type v} {A : Type w}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K]
  [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

/-- The Hodge function of the constructed central-simple positive homomorphism. -/
def realHodgeFunction : (K →+* ℂ) → ℕ :=
  standardHodgeFunction Φ
    ((D.realMatrixEquiv C).toAlgHom.comp (D.realPositiveKottwitzHom C).val.hom)

theorem realHodgeFunction_eq : D.realHodgeFunction C = C.hodgeFunction :=
  C.realHodgeFunction_eq D.totallyRealBasis

/-- The actual datum's reflex field, with its Hodge homomorphism constructed from D. -/
def realReflexField : IntermediateField ℚ ℂ :=
  Shimura.reflexField (D.realHodgeFunction C)

theorem realReflexField_eq : D.realReflexField C = C.reflexField := by
  rw [realReflexField, D.realHodgeFunction_eq]
  rfl

theorem realReflexField_eq_bot (h2 : n = 2) [Subsingleton (E →+* ℝ)] :
    D.realReflexField C = ⊥ :=
  C.realReflexField_eq_bot D.totallyRealBasis h2

/-- Construct the reflex field from signature and CM-section hypotheses. -/
def realReflexFieldOfSignature (h : HasHarrisSignature D.toSecondKindInvolution n)
    (hΦ : IsCMSection E K Φ) : IntermediateField ℚ ℂ :=
  D.realReflexField (HarrisSignatureCharts.ofSignature h hΦ)

variable {F : Type t} [Field F] [NumberField F] [IsCMField F] [IsQuadraticExtension ℚ F]
  {j : F →+* K} {τ₀ : F →+* ℂ}
  (CH : HarrisSignatureCharts D.toSecondKindInvolution n (harrisCMSection E j τ₀))

theorem realReflexField_eq_distinguishedImage
    (h : 3 ≤ n ∨ ∃ τ, τ ≠ CH.distinguished) :
    D.realReflexField CH = CH.distinguishedImage :=
  CH.realReflexField_eq_distinguishedImage D.totallyRealBasis h

end Langlands.Shimura.CentralSimpleUnitaryData
