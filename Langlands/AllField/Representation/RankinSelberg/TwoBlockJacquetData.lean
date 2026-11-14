import Langlands.Representation.RankinSelberg.TwoBlockJacquetData
import Langlands.AllField.Group.GL.CompactOpenSupplement
import Langlands.AllField.Representation.Induction.OppositeParabolic
import Langlands.AllField.Representation.RankinSelberg.MultiplicativityStatement
import Langlands.AllField.Representation.Shahidi.Induction
import Langlands.AllField.Representation.Shahidi.IntertwiningCovariance
/-!
# Two-block scalar sections and absolute Jacquet integral data

JPSS 1983, Section 4.6, printed pages 410-411: for representations `σ_1, σ_2` of
`GL_(m_1+1)(F)` and `GL_(m_2+1)(F)` with `(m_1+1) + (m_2+1) = t+1`, the sections
of the normalized induction from the lower block parabolic satisfy the
covariance (4.6.1), and the integrand of (4.6.2) is a scalar evaluation of a
section at `u g`, for `u` in the complementary upper radical, against the
positive character of the upper-right corner entry of `u`.

This module defines that data for the published actual lower induction
`F.canonicalNormalizedOppositeParabolicInduced B (B.blockTensor σ)` with
`B = succBlockShape m h`: scalar evaluation through supplied linear functionals
on the block carriers, the upper radical matrix, the positive kernel, the raw
integrand, its Bochner integral against a supplied measure and the absolute
integrability conditions. It asserts no convergence.
-/

noncomputable section

open MeasureTheory

namespace Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear

universe uι uF uW uR

section Contraction


end Contraction

section Radical



end Radical

section Kernel



end Kernel

section Sections

variable (F : Type uF) [Field F]
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))

/-- The carrier of the actual lower induction
`(⟨⟩ : LocalFieldData F).normalizedOppositeParabolicInduced B (B.blockTensor σ)`,
`B = succBlockShape m h`: the sections of JPSS (4.6.1). -/
abbrev Sections [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] : Type (max uF uW) :=
  letI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
  Induction.SmoothFunctions ((succBlockShape m h).oppositeParabolic F)
    (twist ((⟨⟩ : LocalFieldData F).oppositeParabolicHalfModulus (succBlockShape m h))
      (((succBlockShape m h).blockTensor σ).comp
        ((succBlockShape m h).oppositeLeviProjection F)))

/-- The actual lower induced representation `I(σ_1 ⊗ σ_2)`, acting on `Sections`. -/
abbrev inducedRep [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    letI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
    Representation ℂ (GeneralLinear (t + 1) F) (Sections F h σ) :=
  (⟨⟩ : LocalFieldData F).normalizedOppositeParabolicInduced (succBlockShape m h)
    ((succBlockShape m h).blockTensor σ)

/-- Evaluation of a section at an ambient element. -/
abbrev sectionEval [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (f : Sections F h σ) (g : GeneralLinear (t + 1) F) :
    PiTensorProduct ℂ W :=
  letI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
  Induction.eval ((succBlockShape m h).oppositeParabolic F)
    (twist ((⟨⟩ : LocalFieldData F).oppositeParabolicHalfModulus (succBlockShape m h))
      (((succBlockShape m h).blockTensor σ).comp
        ((succBlockShape m h).oppositeLeviProjection F))) f g

variable {F h σ}

/-- The scalar section `(g, a) ↦ (⊗ ℓ_i) ((σ_1 ⊗ σ_2)(a) f(g))` at an ambient element `g`
and an actual block Levi element `a`. -/
def scalarSection [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (ell : ∀ i, W i →ₗ[ℂ] ℂ) (f : Sections F h σ)
    (g : GeneralLinear (t + 1) F) (a : (succBlockShape m h).Levi F) : ℂ :=
  tensorContraction ell ((succBlockShape m h).blockTensor σ a (sectionEval F h σ f g))

theorem scalarSection_def [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (ell : ∀ i, W i →ₗ[ℂ] ℂ) (f : Sections F h σ)
    (g : GeneralLinear (t + 1) F) (a : (succBlockShape m h).Levi F) :
    scalarSection ell f g a =
      tensorContraction ell ((succBlockShape m h).blockTensor σ a (sectionEval F h σ f g)) :=
  rfl

@[simp]
theorem scalarSection_one [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (ell : ∀ i, W i →ₗ[ℂ] ℂ) (f : Sections F h σ)
    (g : GeneralLinear (t + 1) F) :
    scalarSection ell f g 1 = tensorContraction ell (sectionEval F h σ f g) := by
  rw [scalarSection_def, map_one, Module.End.one_apply]

@[simp]
theorem sectionEval_add [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (f f' : Sections F h σ) (g : GeneralLinear (t + 1) F) :
    letI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
    sectionEval F h σ (f + f') g = sectionEval F h σ f g + sectionEval F h σ f' g :=
  rfl

@[simp]
theorem sectionEval_smul [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (c : ℂ) (f : Sections F h σ) (g : GeneralLinear (t + 1) F) :
    letI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
    sectionEval F h σ (c • f) g = c • sectionEval F h σ f g :=
  rfl

@[simp]
theorem sectionEval_zero [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (g : GeneralLinear (t + 1) F) :
    letI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
    sectionEval F h σ 0 g = 0 :=
  rfl

@[simp]
theorem scalarSection_add [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (ell : ∀ i, W i →ₗ[ℂ] ℂ) (f f' : Sections F h σ)
    (g : GeneralLinear (t + 1) F) (a : (succBlockShape m h).Levi F) :
    letI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
    scalarSection ell (f + f') g a = scalarSection ell f g a + scalarSection ell f' g a := by
  simp only [scalarSection_def, sectionEval_add, map_add]

@[simp]
theorem scalarSection_smul [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (ell : ∀ i, W i →ₗ[ℂ] ℂ) (c : ℂ) (f : Sections F h σ)
    (g : GeneralLinear (t + 1) F) (a : (succBlockShape m h).Levi F) :
    letI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
    scalarSection ell (c • f) g a = c * scalarSection ell f g a := by
  simp only [scalarSection_def, sectionEval_smul, map_smul, smul_eq_mul]

/-- Compatibility with the actual induced right translation. -/
@[simp]
theorem scalarSection_inducedRep [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (ell : ∀ i, W i →ₗ[ℂ] ℂ)
    (g' : GeneralLinear (t + 1) F) (f : Sections F h σ)
    (g : GeneralLinear (t + 1) F) (a : (succBlockShape m h).Levi F) :
    scalarSection ell (inducedRep F h σ g' f) g a = scalarSection ell f (g * g') a :=
  rfl

/-- The covariance (4.6.1) of scalar sections: if the lower parabolic element `q`
has Levi projection `b`, then the value at `(q g, a)` is `δ_P(b)^(-1/2)` times the
value at `(g, a b)`, for the upper block modulus `δ_P`. -/
theorem scalarSection_covariant [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (ell : ∀ i, W i →ₗ[ℂ] ℂ) (f : Sections F h σ)
    (q : (succBlockShape m h).oppositeParabolic F)
    {b : (succBlockShape m h).Levi F}
    (hq : (succBlockShape m h).oppositeLeviProjection F q = b)
    (g : GeneralLinear (t + 1) F) (a : (succBlockShape m h).Levi F) :
    scalarSection ell f ((q : GeneralLinear (t + 1) F) * g) a =
      (((⟨⟩ : LocalFieldData F).leviHalfModulus (succBlockShape m h) b : ℂˣ) : ℂ)⁻¹ *
        scalarSection ell f g (a * b) := by
  subst hq
  rw [scalarSection_def, sectionEval,
    (⟨⟩ : LocalFieldData F).normalizedOppositeParabolicInduced_covariant, map_smul,
    map_smul, scalarSection_def, map_mul, Module.End.mul_apply,
    Langlands.LocalFieldData.leviHalfModulus_apply, smul_eq_mul]

end Sections

section Integral

variable {F : Type uF} [Field F]
variable {t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)}
variable [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F)
variable (ell : ∀ i, W i →ₗ[ℂ] ℂ)

/-- The raw scalar integrand of JPSS (4.6.2):
`x ↦ ⟨f(u(x) g), ⊗ ℓ_i⟩ ψ(x_(m 0, 0))`. -/
def integrand (f : Sections F h σ) (g : GeneralLinear (t + 1) F)
    (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) : ℂ :=
  scalarSection ell f (upperRadical h F x * g) 1 * positiveKernel ψ x

theorem integrand_def (f : Sections F h σ) (g : GeneralLinear (t + 1) F)
    (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) :
    integrand ψ ell f g x =
      scalarSection ell f (upperRadical h F x * g) 1 * positiveKernel ψ x :=
  rfl

/-- The integrand with the kernel evaluated at the corner entry. -/
theorem integrand_apply (f : Sections F h σ) (g : GeneralLinear (t + 1) F)
    (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) :
    integrand ψ ell f g x =
      tensorContraction ell (sectionEval F h σ f (upperRadical h F x * g)) *
        ψ.complex (x (Fin.last (m 0)) 0) := by
  rw [integrand_def, scalarSection_one, positiveKernel_apply]

@[simp]
theorem integrand_add (f f' : Sections F h σ) (g : GeneralLinear (t + 1) F)
    (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) :
    letI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
    integrand ψ ell (f + f') g x = integrand ψ ell f g x + integrand ψ ell f' g x := by
  simp only [integrand_def, scalarSection_add, add_mul]

@[simp]
theorem integrand_smul (c : ℂ) (f : Sections F h σ) (g : GeneralLinear (t + 1) F)
    (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) :
    letI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
    integrand ψ ell (c • f) g x = c * integrand ψ ell f g x := by
  simp only [integrand_def, scalarSection_smul, mul_assoc]

/-- Raw right translation: translating the section by `g'` translates the integrand's
ambient argument. -/
@[simp]
theorem integrand_inducedRep (g' : GeneralLinear (t + 1) F) (f : Sections F h σ)
    (g : GeneralLinear (t + 1) F) :
    integrand ψ ell (inducedRep F h σ g' f) g = integrand ψ ell f (g * g') := by
  funext x
  rw [integrand_def, integrand_def, scalarSection_inducedRep, mul_assoc]

variable [MeasurableSpace F]
variable (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F))

/-- The function `g ↦ ∫ ⟨f(u g), ⊗ ℓ_i⟩ ψ(u) du` of JPSS (4.6.2), as the ordinary
Bochner integral against the supplied measure `μ` on the rectangular coordinates. -/
def jacquetFunction (f : Sections F h σ) (g : GeneralLinear (t + 1) F) : ℂ :=
  ∫ x, integrand ψ ell f g x ∂μ

theorem jacquetFunction_def (f : Sections F h σ) (g : GeneralLinear (t + 1) F) :
    jacquetFunction ψ ell μ f g = ∫ x, integrand ψ ell f g x ∂μ :=
  rfl

/-- The integral written out with the corner kernel. -/
theorem jacquetFunction_apply (f : Sections F h σ) (g : GeneralLinear (t + 1) F) :
    jacquetFunction ψ ell μ f g =
      ∫ x, tensorContraction ell (sectionEval F h σ f (upperRadical h F x * g)) *
        ψ.complex (x (Fin.last (m 0)) 0) ∂μ := by
  rw [jacquetFunction_def]
  exact integral_congr_ae (Filter.Eventually.of_forall (integrand_apply ψ ell f g))

/-- Absolute integrability of the integrand at `g`. -/
def IsAbsIntegrableAt (f : Sections F h σ) (g : GeneralLinear (t + 1) F) : Prop :=
  Integrable (integrand ψ ell f g) μ

/-- Absolute integrability of the integrand at every `g`. -/
def IsAbsIntegrable (f : Sections F h σ) : Prop :=
  ∀ g, IsAbsIntegrableAt ψ ell μ f g

/-- Additivity of the integral under absolute integrability of both integrands. -/
theorem jacquetFunction_add {f f' : Sections F h σ} {g : GeneralLinear (t + 1) F}
    (hf : IsAbsIntegrableAt ψ ell μ f g) (hf' : IsAbsIntegrableAt ψ ell μ f' g) :
    letI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
    jacquetFunction ψ ell μ (f + f') g = jacquetFunction ψ ell μ f g + jacquetFunction ψ ell μ f' g := by
  let := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
  simp only [jacquetFunction_def, integrand_add]
  exact integral_add hf hf'

/-- Complex homogeneity of the integral. -/
theorem jacquetFunction_smul (c : ℂ) (f : Sections F h σ) (g : GeneralLinear (t + 1) F) :
    letI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
    jacquetFunction ψ ell μ (c • f) g = c * jacquetFunction ψ ell μ f g := by
  let := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
  simp only [jacquetFunction_def, integrand_smul]
  exact integral_const_mul c _

/-- Raw right translation of the integral. -/
@[simp]
theorem jacquetFunction_inducedRep (g' : GeneralLinear (t + 1) F) (f : Sections F h σ)
    (g : GeneralLinear (t + 1) F) :
    jacquetFunction ψ ell μ (inducedRep F h σ g' f) g = jacquetFunction ψ ell μ f (g * g') := by
  rw [jacquetFunction_def, jacquetFunction_def, integrand_inducedRep]

end Integral

end Langlands.AllField.RankinSelberg.TwoBlockJacquet
