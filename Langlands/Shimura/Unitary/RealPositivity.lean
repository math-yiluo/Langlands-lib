import Langlands.Shimura.Unitary.RealSplitting
import Langlands.Shimura.Unitary.Positivity

noncomputable section
universe u v w z
open NumberField Module Algebra
open scoped TensorProduct Classical

namespace Langlands.Shimura

/-- Regular trace is preserved by an algebra equivalence. -/
theorem trace_mulLeft_algEquiv {R A B : Type*} [CommRing R] [Ring A] [Ring B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (x : A) :
    LinearMap.trace R B (LinearMap.mulLeft R (e x)) =
      LinearMap.trace R A (LinearMap.mulLeft R x) := by
  have he : e.toLinearEquiv.conj (LinearMap.mulLeft R x) =
      LinearMap.mulLeft R (e x) := by
    ext y
    simp [LinearEquiv.conj_apply, map_mul]
  rw [← he, LinearMap.trace_conj']

namespace AlgebraInvolution

/-- Positivity is invariant under an involution-compatible real algebra equivalence. -/
theorem isPositive_iff_of_algEquiv {A B : Type*} [Ring A] [Ring B]
    [Algebra ℝ A] [Algebra ℝ B] (σ : AlgebraInvolution ℝ A)
    (τ : AlgebraInvolution ℝ B) (e : A ≃ₐ[ℝ] B)
    (he : ∀ x, e (σ x) = τ (e x)) : σ.IsPositive ↔ τ.IsPositive := by
  have ht (x : A) :
      LinearMap.trace ℝ B (LinearMap.mulLeft ℝ (τ (e x) * e x)) =
        LinearMap.trace ℝ A (LinearMap.mulLeft ℝ (σ x * x)) := by
    rw [← he, ← _root_.map_mul]
    exact trace_mulLeft_algEquiv e _
  constructor
  · intro h y hy
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [ht]
    exact h x (fun hx => hy (by simp [hx]))
  · intro h x hx
    rw [← ht]
    exact h (e x) (fun he0 => hx (e.injective (he0.trans e.map_zero.symm)))

/-- Compatible complex homomorphisms equipped with positivity of their actual twist. -/
def PositiveComplexHom {A : Type*} [Ring A] [Algebra ℝ A]
    (σ : AlgebraInvolution ℝ A) :=
  {h : ComplexHom σ // h.twist.IsPositive}

namespace PositiveComplexHom

variable {A : Type*} [Ring A] [Algebra ℝ A] {σ : AlgebraInvolution ℝ A}

/-- Conjugation preserves the positivity certificate because it preserves the twist. -/
def conj (h : PositiveComplexHom σ) : PositiveComplexHom σ :=
  ⟨h.val.conj, fun x hx => by
    change 0 < LinearMap.trace ℝ A (LinearMap.mulLeft ℝ (h.val.conj.twist x * x))
    rw [ComplexHom.twist_conj]
    exact h.property x hx⟩

@[simp] theorem conj_val (h : PositiveComplexHom σ) : h.conj.val = h.val.conj := rfl

end PositiveComplexHom
end AlgebraInvolution

namespace HarrisSignatureCharts

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

/-- The actual twisted involution is conjugate transpose in the assembled matrix coordinates. -/
theorem realComplexHom_twist_matrix (x : ℝ ⊗[ℚ] A) :
    C.realMatrixEquiv b ((C.realComplexHom b).twist x) =
      piConjTranspose n (E →+* ℝ) (C.realMatrixEquiv b x) := by
  rw [AlgebraInvolution.ComplexHom.twist_apply, map_mul, map_mul,
    C.realMatrixEquiv_involution b]
  funext τ
  change C.realMatrixEquiv b ((C.realComplexHom b).hom (-Complex.I)) τ *
      signatureAdjoint n (if τ = C.distinguished then n - 1 else n)
        (C.realMatrixEquiv b x τ) *
      C.realMatrixEquiv b ((C.realComplexHom b).hom Complex.I) τ = _
  rw [C.realComplexHom_matrix, C.realComplexHom_matrix]
  exact correctedComplexHom_twist n _ _

theorem realComplexHom_twist_isPositive : (C.realComplexHom b).twist.IsPositive :=
  (AlgebraInvolution.isPositive_iff_of_algEquiv _ _ (C.realMatrixEquiv b)
    (C.realComplexHom_twist_matrix b)).mpr (piConjTranspose_isPositive n (E →+* ℝ))

/-- Construct the positive homomorphism on the original algebra's actual real scalar extension. -/
def realPositiveComplexHom :
    AlgebraInvolution.PositiveComplexHom (σ.rationalInvolution.baseChange ℝ) :=
  ⟨C.realComplexHom b, C.realComplexHom_twist_isPositive b⟩

@[simp] theorem realPositiveComplexHom_val :
    (C.realPositiveComplexHom b).val = C.realComplexHom b := rfl

/-- Kottwitz's conjugate homomorphism on the original real algebra, with proved positivity. -/
def realPositiveKottwitzHom :
    AlgebraInvolution.PositiveComplexHom (σ.rationalInvolution.baseChange ℝ) :=
  (C.realPositiveComplexHom b).conj

@[simp] theorem realPositiveKottwitzHom_val :
    (C.realPositiveKottwitzHom b).val = (C.realComplexHom b).conj := rfl

end HarrisSignatureCharts

namespace CentralSimpleUnitaryData

variable {E : Type u} {K : Type v} {A : Type w}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K]
  [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

/-- The actual central-simple algebra homomorphism has a positive twisted involution. -/
theorem realComplexHom_twist_isPositive : (D.realComplexHom C).twist.IsPositive :=
  C.realComplexHom_twist_isPositive D.totallyRealBasis

def realPositiveComplexHom :
    AlgebraInvolution.PositiveComplexHom
      (D.toSecondKindInvolution.rationalInvolution.baseChange ℝ) :=
  C.realPositiveComplexHom D.totallyRealBasis

@[simp] theorem realPositiveComplexHom_val :
    (D.realPositiveComplexHom C).val = D.realComplexHom C := rfl

/-- Kottwitz's actual complex algebra homomorphism, including its positivity certificate. -/
def realPositiveKottwitzHom :
    AlgebraInvolution.PositiveComplexHom
      (D.toSecondKindInvolution.rationalInvolution.baseChange ℝ) :=
  (D.realPositiveComplexHom C).conj

@[simp] theorem realPositiveKottwitzHom_val :
    (D.realPositiveKottwitzHom C).val = (D.realComplexHom C).conj := rfl

/-- Signature and CM-section inputs construct the positive Kottwitz homomorphism. -/
def realPositiveKottwitzHomOfSignature (h : HasHarrisSignature D.toSecondKindInvolution n)
    (hΦ : IsCMSection E K Φ) :
    AlgebraInvolution.PositiveComplexHom
      (D.toSecondKindInvolution.rationalInvolution.baseChange ℝ) :=
  D.realPositiveKottwitzHom (HarrisSignatureCharts.ofSignature h hΦ)

end CentralSimpleUnitaryData
end Langlands.Shimura
