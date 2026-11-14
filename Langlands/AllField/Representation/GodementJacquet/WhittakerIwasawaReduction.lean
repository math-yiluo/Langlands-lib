import Langlands.Representation.GodementJacquet.WhittakerIwasawaReduction
import Langlands.AllField.HarmonicAnalysis.ConductorSupplement
import Langlands.AllField.Representation.GodementJacquet.WhittakerCosetSum
import Langlands.AllField.Representation.GodementJacquet.WhittakerSliceSchwartz
import Langlands.AllField.Representation.GodementJacquet.WhittakerTorusMellin
import Langlands.AllField.Representation.RankinSelberg.DeterminantSlicesSupplement
import Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatementSupplement
import Langlands.AllField.Representation.RankinSelberg.IntegralDeterminant
import Langlands.AllField.Representation.RankinSelberg.IwasawaHaarIntegration
import Langlands.AllField.Representation.RankinSelberg.UnequalRankIwasawaSupportProof
import Langlands.AllField.Representation.Whittaker.SmoothSimpleRootSupportProof
/-!
# Iwasawa reduction of full-matrix Whittaker integrals

The analytic properties of a Whittaker function `W` on `GL_(n+1)(F)` used for
the convergence and rationality of `∫ Φ(g) W(g) |det g|^s dg`, and the first
reduction steps: Iwasawa integration `G = N A K` in the canonical
normalization, the factorization of the integrand at `u diag(a) k`, its
unipotent integral as a slice integral of `Φ`, and the finite coset sum over
`K`. See the paired Markdown.
-/

noncomputable section

namespace Langlands.AllField.GodementJacquet.WhittakerTorus
open Langlands.GodementJacquet.WhittakerTorus
open Langlands.AllField.GodementJacquet.WhittakerTorus
open Langlands.GodementJacquet
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement FiniteFunctionMellinStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable unequalRankIwasawaSupport zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg
open Langlands.Whittaker hiding smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open scoped BigOperators ENNReal

universe uF

namespace Padic
open Langlands.GodementJacquet.WhittakerTorus.Padic hiding HasTorusExpansion IsWhittakerLike borelModulus initTail integralK integral_iwasawa integral_unipotent_matrixIntegrand iwasawaReductionBorelSpace iwasawaReductionLocalField iwasawaReductionMeasurableSpace iwasawaReductionTopology iwasawaReductionUnipotentBorelSpace iwasawaReductionUnipotentMeasurableSpace iwasawaReductionUnitsBorelSpace iwasawaReductionUnitsMeasurableSpace iwasawaReductionValuativeRel lintegral_iwasawa lintegral_unipotent_matrixIntegrand matrixIntegrand_iwasawa matrixIntegrand_mul_right normalizedAbs_det_integralK ratios torusIntegrand torusIntegrand_tailProd torusMellin torusMellinLocalField torusMellinTopology torusMellinUnitsBorelSpace torusMellinUnitsMeasurableSpace torusMellinValuativeRel
open Langlands.AllField.GodementJacquet.WhittakerTorus.Padic
open Langlands.GodementJacquet.WhittakerTorus
open Langlands.AllField.GodementJacquet.WhittakerTorus
open Langlands.GodementJacquet
open Langlands.AllField.GodementJacquet

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance iwasawaReductionUnitsMeasurableSpace : MeasurableSpace Fˣ := borel _
local instance iwasawaReductionUnitsBorelSpace : BorelSpace Fˣ := ⟨rfl⟩
local instance iwasawaReductionMeasurableSpace (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F) :=
  borel _
local instance iwasawaReductionBorelSpace (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance iwasawaReductionUnipotentMeasurableSpace (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F) := borel _
local instance iwasawaReductionUnipotentBorelSpace (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩

variable {n : ℕ}

/-- The integral subgroup `K = GL_(n+1)(O)`. -/
abbrev integralK (n : ℕ) : Subgroup (Langlands.GeneralLinear (n + 1) F) :=
  Conductor.integralSubgroup (ValuativeRel.valuation F).integer n

/-- The upper-Borel modulus `δ(a) = ∏_{i<j} |a_i / a_j|`. -/
def borelModulus (a : Fin (n + 1) → Fˣ) : ℝ :=
  ∏ i : Fin (n + 1), ∏ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => i < j),
    (⟨⟩ : LocalFieldData F).normalizedAbs ((a i / a j : Fˣ) : F)

/-- A torus expansion `f(a) = Σ_{χ ∈ X} φ_χ(a_0/a_1, …, a_(n-1)/a_n) χ(a)`, with a
finite set `X` of finite functions and Schwartz–Bruhat coefficients `φ_χ`. -/
def HasTorusExpansion (f : (Fin (n + 1) → Fˣ) → ℂ) : Prop :=
  ∃ X : Finset ((Fin (n + 1) → Fˣ) → ℂ), (∀ χ ∈ X, IsFiniteFunction χ) ∧
    ∃ φ : ((Fin (n + 1) → Fˣ) → ℂ) → SchwartzBruhat (Fin n → F),
      ∀ a, f a = ∑ χ ∈ X, φ χ (ratios F a) * χ a

/-- The properties of a function `W` on `GL_(n+1)(F)` used to prove convergence
and rationality of its full-matrix integrals: continuity, left equivariance
under the standard character of the upper unipotent group, right invariance
under an open subgroup, and a torus expansion of every right translate. -/
structure IsWhittakerLike (ψ : UnitaryAdditiveCharacter F)
    (W : Langlands.GeneralLinear (n + 1) F → ℂ) : Prop where
  continuous : Continuous W
  equivariant : ∀ (u : upperUnipotent (n + 1) F) g,
    W (u.val * g) = (standardCharacter ψ n u : ℂ) * W g
  smooth : ∃ L : OpenSubgroup (Langlands.GeneralLinear (n + 1) F),
    ∀ g, ∀ k ∈ L, W (g * k) = W g
  expansion : ∀ k, HasTorusExpansion F (fun a => W (Iwasawa.diagonalUnits a * k))

/-- **Iwasawa integration**, lower Lebesgue form:
`∫_G f = ∫_K ∫_A δ(a)⁻¹ ∫_N f(u diag(a) k) du da dk`. -/
theorem lintegral_iwasawa (f : Langlands.GeneralLinear (n + 1) F → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ g, f g ∂generalLinearHaar F n =
      ∫⁻ k in (integralK F n : Set (Langlands.GeneralLinear (n + 1) F)),
        ∫⁻ a, ENNReal.ofReal ((borelModulus F a)⁻¹) *
          ∫⁻ u, f (u.val * Iwasawa.diagonalUnits a * k) ∂unipotentHaar F n
          ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar F)
        ∂generalLinearHaar F n := by
  have : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
  have : SecondCountableTopology F := (⟨⟩ : LocalFieldData F).secondCountableTopology
  refine IwasawaHaar.lintegral_generalLinearHaar
    (fun a => ENNReal.ofReal ((borelModulus F a)⁻¹)) (fun a => ?_) f hf
  rw [diagonalConj_map F (⟨⟩ : LocalFieldData F) n a, ENNReal.smul_def]
  congr 1
  unfold borelModulus
  rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_inv, singleton_modulus_real F _ a]

/-- **Iwasawa integration**, Bochner form for integrable complex functions. -/
theorem integral_iwasawa (f : Langlands.GeneralLinear (n + 1) F → ℂ)
    (hf : Integrable f (generalLinearHaar F n)) :
    ∫ g, f g ∂generalLinearHaar F n =
      ∫ k in (integralK F n : Set (Langlands.GeneralLinear (n + 1) F)),
        ∫ a, (((borelModulus F a)⁻¹ : ℝ) : ℂ) *
          ∫ u, f (u.val * Iwasawa.diagonalUnits a * k) ∂unipotentHaar F n
          ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar F)
        ∂generalLinearHaar F n :=
  Langlands.AllField.RankinSelberg.IwasawaHaar.integral_generalLinearHaar_iwasawa F (⟨⟩ : LocalFieldData F) n f hf

/-- The normalized absolute value of the determinant of an element of `K` is one. -/
theorem normalizedAbs_det_integralK {k : Langlands.GeneralLinear (n + 1) F}
    (hk : k ∈ integralK F n) :
    normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) (Matrix.det k.val) = 1 :=
  normalizedAbs_det_of_mem_integralSubgroup (⟨⟩ : LocalFieldData F) hk

/-- The matrix integrand at `u diag(a) k`, for `k ∈ K` and a left-equivariant
`W`, is `(W(diag(a) k) |∏ a_i|^s) · (Φ(u diag(a) k) ψ_N(u))`. -/
theorem matrixIntegrand_iwasawa {ψ : UnitaryAdditiveCharacter F}
    {W : Langlands.GeneralLinear (n + 1) F → ℂ}
    (hW : ∀ (u : upperUnipotent (n + 1) F) g,
      W (u.val * g) = (standardCharacter ψ n u : ℂ) * W g)
    (Φ : MatrixTestFunction n F) (s : ℂ) (u : upperUnipotent (n + 1) F)
    (a : Fin (n + 1) → Fˣ) {k : Langlands.GeneralLinear (n + 1) F}
    (hk : k ∈ integralK F n) :
    Langlands.AllField.GodementJacquet.Padic.matrixIntegrand F Φ s W (u.val * Iwasawa.diagonalUnits a * k) =
      (W (Iwasawa.diagonalUnits a * k) *
        (((⟨⟩ : LocalFieldData F).normalizedAbs (∏ i, (a i : F)) : ℝ) : ℂ) ^ s) *
      (Φ (u.val.val * Matrix.diagonal (fun i => (a i : F)) * k.val) *
        (standardCharacter ψ n u : ℂ)) := by
  have hdet : normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)
      (Matrix.det (Iwasawa.diagonalUnits a * k).val) =
      (⟨⟩ : LocalFieldData F).normalizedAbs (∏ i, (a i : F)) := by
    rw [Units.val_mul, Matrix.det_mul, map_mul, normalizedAbs_det_integralK F hk, mul_one,
      Iwasawa.diagonalUnits_val, Matrix.det_diagonal]
    rfl
  have hval : (u.val * Iwasawa.diagonalUnits a * k).val =
      u.val.val * Matrix.diagonal (fun i => (a i : F)) * k.val := by
    rw [Units.val_mul, Units.val_mul, Iwasawa.diagonalUnits_val]
  simp only [Langlands.AllField.GodementJacquet.Padic.matrixIntegrand, GodementJacquet.matrixIntegrand]
  rw [hval, mul_assoc u.val, determinantWeight_unipotent_mul, hW u, determinantWeight, hdet]
  ring

/-- The unipotent integral of the matrix integrand at `u diag(a) k`, for
`k ∈ K`, is `W(diag(a) k) |∏ a_i|^s` times the slice integral of `Φ(· k)`. -/
theorem integral_unipotent_matrixIntegrand {ψ : UnitaryAdditiveCharacter F}
    {W : Langlands.GeneralLinear (n + 1) F → ℂ}
    (hW : ∀ (u : upperUnipotent (n + 1) F) g,
      W (u.val * g) = (standardCharacter ψ n u : ℂ) * W g)
    (Φ : MatrixTestFunction n F) (s : ℂ) (a : Fin (n + 1) → Fˣ)
    {k : Langlands.GeneralLinear (n + 1) F} (hk : k ∈ integralK F n) :
    ∫ u, Langlands.AllField.GodementJacquet.Padic.matrixIntegrand F Φ s W (u.val * Iwasawa.diagonalUnits a * k)
        ∂unipotentHaar F n =
      W (Iwasawa.diagonalUnits a * k) *
        (((⟨⟩ : LocalFieldData F).normalizedAbs (∏ i, (a i : F)) : ℝ) : ℂ) ^ s *
        Langlands.AllField.GodementJacquet.WhittakerSlice.sliceIntegral F ψ (fun M => Φ (M * k.val))
          (fun i => (a i : F)) := by
  simp_rw [matrixIntegrand_iwasawa F hW Φ s _ a hk]
  rw [integral_const_mul]
  rfl

/-- The unipotent integral of the norm of the matrix integrand at `u diag(a) k`,
for `k ∈ K`. -/
theorem lintegral_unipotent_matrixIntegrand {ψ : UnitaryAdditiveCharacter F}
    {W : Langlands.GeneralLinear (n + 1) F → ℂ}
    (hW : ∀ (u : upperUnipotent (n + 1) F) g,
      W (u.val * g) = (standardCharacter ψ n u : ℂ) * W g)
    (Φ : MatrixTestFunction n F) (s : ℂ) (a : Fin (n + 1) → Fˣ)
    {k : Langlands.GeneralLinear (n + 1) F} (hk : k ∈ integralK F n) :
    ∫⁻ u, ‖Langlands.AllField.GodementJacquet.Padic.matrixIntegrand F Φ s W
        (u.val * Iwasawa.diagonalUnits a * k)‖ₑ ∂unipotentHaar F n =
      ‖W (Iwasawa.diagonalUnits a * k) *
        (((⟨⟩ : LocalFieldData F).normalizedAbs (∏ i, (a i : F)) : ℝ) : ℂ) ^ s‖ₑ *
      ∫⁻ u, ‖Φ (u.val.val * Matrix.diagonal (fun i => (a i : F)) * k.val)‖ₑ
        ∂unipotentHaar F n := by
  have h1 : ∀ u : upperUnipotent (n + 1) F, ‖(standardCharacter ψ n u : ℂ)‖ₑ = 1 :=
    fun u => by rw [← ofReal_norm, norm_standardCharacter, ENNReal.ofReal_one]
  have hne : ‖W (Iwasawa.diagonalUnits a * k)‖ₑ *
      ‖(((⟨⟩ : LocalFieldData F).normalizedAbs (∏ i, (a i : F)) : ℝ) : ℂ) ^ s‖ₑ ≠
        ⊤ :=
    ENNReal.mul_ne_top enorm_ne_top enorm_ne_top
  simp_rw [matrixIntegrand_iwasawa F hW Φ s _ a hk, enorm_mul, h1, mul_one]
  rw [lintegral_const_mul' _ _ hne]

/-- The matrix integrand is right invariant under `k₀ ∈ K` fixing `Φ` and `W`. -/
theorem matrixIntegrand_mul_right {W : Langlands.GeneralLinear (n + 1) F → ℂ}
    (Φ : MatrixTestFunction n F) (s : ℂ)
    {k₀ : Langlands.GeneralLinear (n + 1) F} (hk₀ : k₀ ∈ integralK F n)
    (hΦ : ∀ M, Φ (M * k₀.val) = Φ M) (hW : ∀ g, W (g * k₀) = W g)
    (g : Langlands.GeneralLinear (n + 1) F) :
    Langlands.AllField.GodementJacquet.Padic.matrixIntegrand F Φ s W (g * k₀) =
      Langlands.AllField.GodementJacquet.Padic.matrixIntegrand F Φ s W g := by
  simp only [Langlands.AllField.GodementJacquet.Padic.matrixIntegrand, GodementJacquet.matrixIntegrand,
    determinantWeight]
  rw [Units.val_mul, hΦ, hW, Matrix.det_mul, map_mul, normalizedAbs_det_integralK F hk₀, mul_one]

/-- **Finite coset reduction.** For `W` as in `IsWhittakerLike` and a test
function `Φ`, there are an open subgroup `K₀ ≤ K` and a finite set `S ⊆ K` such
that the matrix integrand is right invariant under `K₀` for every `s`, and the
integral over `K` of every right-`K₀`-invariant function is the sum of its
values on `S` times the mass of `K₀`. -/
theorem IsWhittakerLike.exists_cosetSum {ψ : UnitaryAdditiveCharacter F}
    {W : Langlands.GeneralLinear (n + 1) F → ℂ} (hW : IsWhittakerLike F ψ W)
    (Φ : MatrixTestFunction n F) :
    ∃ (K₀ : OpenSubgroup (Langlands.GeneralLinear (n + 1) F))
      (S : Finset (Langlands.GeneralLinear (n + 1) F)),
      (K₀ : Subgroup (Langlands.GeneralLinear (n + 1) F)) ≤ integralK F n ∧
      (S : Set (Langlands.GeneralLinear (n + 1) F)) ⊆ integralK F n ∧
      (∀ s g, ∀ k₀ ∈ K₀, Langlands.AllField.GodementJacquet.Padic.matrixIntegrand F Φ s W (g * k₀) =
        Langlands.AllField.GodementJacquet.Padic.matrixIntegrand F Φ s W g) ∧
      (∀ f : Langlands.GeneralLinear (n + 1) F → ℝ≥0∞,
        (∀ k ∈ integralK F n, ∀ k₀ ∈ K₀, f (k * k₀) = f k) →
        ∫⁻ x in (integralK F n : Set (Langlands.GeneralLinear (n + 1) F)),
            f x ∂generalLinearHaar F n =
          ∑ k ∈ S, generalLinearHaar F n
            (K₀ : Set (Langlands.GeneralLinear (n + 1) F)) * f k) ∧
      (∀ f : Langlands.GeneralLinear (n + 1) F → ℂ,
        (∀ k ∈ integralK F n, ∀ k₀ ∈ K₀, f (k * k₀) = f k) →
        ∫ x in (integralK F n : Set (Langlands.GeneralLinear (n + 1) F)),
            f x ∂generalLinearHaar F n =
          ∑ k ∈ S, ((generalLinearHaar F n).real
            (K₀ : Set (Langlands.GeneralLinear (n + 1) F)) : ℂ) * f k) := by
  obtain ⟨L, hL⟩ := hW.smooth
  obtain ⟨K₀, hK₀K, hK₀⟩ := Langlands.AllField.GodementJacquet.CosetSum.Padic.exists_openSubgroup_rightInvariant F Φ W L hL
  obtain ⟨S, hSK, hlin, hint⟩ := CosetSum.exists_cosetSum (generalLinearHaar F n)
    (integralK F n) (K₀ : Subgroup (Langlands.GeneralLinear (n + 1) F))
    (Langlands.AllField.GodementJacquet.CosetSum.Padic.isCompact_integralSubgroup F) K₀.isOpen hK₀K
  exact ⟨K₀, S, hK₀K, hSK, fun s g k₀ hk₀ =>
    matrixIntegrand_mul_right F Φ s (hK₀K hk₀) (hK₀ k₀ hk₀).1 (hK₀ k₀ hk₀).2 g, hlin, hint⟩

end Padic

end Langlands.AllField.GodementJacquet.WhittakerTorus
