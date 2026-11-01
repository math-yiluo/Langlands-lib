import Langlands.Representation.GodementJacquet.WhittakerTorusMellin
import Langlands.Representation.GodementJacquet.WhittakerSliceSchwartz
import Langlands.Representation.GodementJacquet.WhittakerCosetSum
import Langlands.Representation.RankinSelberg.IwasawaHaarIntegration
import Langlands.Representation.RankinSelberg.WeightedWhittakerSquareReduction

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

namespace Langlands.GodementJacquet.WhittakerTorus

open MeasureTheory HarmonicAnalysis RankinSelberg Whittaker GeneralLinear
open scoped BigOperators ENNReal

universe uF

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance iwasawaReductionTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance iwasawaReductionValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance iwasawaReductionLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance iwasawaReductionUnitsMeasurableSpace : MeasurableSpace F.Carrierˣ := borel _
local instance iwasawaReductionUnitsBorelSpace : BorelSpace F.Carrierˣ := ⟨rfl⟩
local instance iwasawaReductionMeasurableSpace (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  borel _
local instance iwasawaReductionBorelSpace (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance iwasawaReductionUnipotentMeasurableSpace (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance iwasawaReductionUnipotentBorelSpace (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩

variable {n : ℕ}

/-- The integral subgroup `K = GL_(n+1)(O)`. -/
abbrev integralK (n : ℕ) : Subgroup (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n

/-- The upper-Borel modulus `δ(a) = ∏_{i<j} |a_i / a_j|`. -/
def borelModulus (a : Fin (n + 1) → F.Carrierˣ) : ℝ :=
  ∏ i : Fin (n + 1), ∏ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => i < j),
    F.canonicalTopologicalData.normalizedAbs ((a i / a j : F.Carrierˣ) : F.Carrier)

/-- A torus expansion `f(a) = Σ_{χ ∈ X} φ_χ(a_0/a_1, …, a_(n-1)/a_n) χ(a)`, with a
finite set `X` of finite functions and Schwartz–Bruhat coefficients `φ_χ`. -/
def HasTorusExpansion (f : (Fin (n + 1) → F.Carrierˣ) → ℂ) : Prop :=
  ∃ X : Finset ((Fin (n + 1) → F.Carrierˣ) → ℂ), (∀ χ ∈ X, IsFiniteFunction χ) ∧
    ∃ φ : ((Fin (n + 1) → F.Carrierˣ) → ℂ) → SchwartzBruhat (Fin n → F.Carrier),
      ∀ a, f a = ∑ χ ∈ X, φ χ (ratios F a) * χ a

/-- The properties of a function `W` on `GL_(n+1)(F)` used to prove convergence
and rationality of its full-matrix integrals: continuity, left equivariance
under the standard character of the upper unipotent group, right invariance
under an open subgroup, and a torus expansion of every right translate. -/
structure IsWhittakerLike (ψ : UnitaryAdditiveCharacter F.Carrier)
    (W : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ) : Prop where
  continuous : Continuous W
  equivariant : ∀ (u : upperUnipotent (n + 1) F.Carrier) g,
    W (u.val * g) = (standardCharacter ψ n u : ℂ) * W g
  smooth : ∃ L : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier),
    ∀ g, ∀ k ∈ L, W (g * k) = W g
  expansion : ∀ k, HasTorusExpansion F (fun a => W (Iwasawa.diagonalUnits a * k))

/-- **Iwasawa integration**, lower Lebesgue form:
`∫_G f = ∫_K ∫_A δ(a)⁻¹ ∫_N f(u diag(a) k) du da dk`. -/
theorem lintegral_iwasawa (f : Langlands.GeneralLinear (n + 1) F.Carrier → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ g, f g ∂generalLinearHaar F.Carrier n =
      ∫⁻ k in (integralK F n : Set (Langlands.GeneralLinear (n + 1) F.Carrier)),
        ∫⁻ a, ENNReal.ofReal ((borelModulus F a)⁻¹) *
          ∫⁻ u, f (u.val * Iwasawa.diagonalUnits a * k) ∂unipotentHaar F.Carrier n
          ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar F.Carrier)
        ∂generalLinearHaar F.Carrier n := by
  have : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
  have : SecondCountableTopology F.Carrier := F.canonicalTopologicalData.secondCountableTopology
  refine IwasawaHaar.lintegral_generalLinearHaar
    (fun a => ENNReal.ofReal ((borelModulus F a)⁻¹)) (fun a => ?_) f hf
  rw [diagonalConj_map F F.canonicalTopologicalData n a, ENNReal.smul_def]
  congr 1
  unfold borelModulus
  rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_inv, singleton_modulus_real F _ a]

/-- **Iwasawa integration**, Bochner form for integrable complex functions. -/
theorem integral_iwasawa (f : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ)
    (hf : Integrable f (generalLinearHaar F.Carrier n)) :
    ∫ g, f g ∂generalLinearHaar F.Carrier n =
      ∫ k in (integralK F n : Set (Langlands.GeneralLinear (n + 1) F.Carrier)),
        ∫ a, (((borelModulus F a)⁻¹ : ℝ) : ℂ) *
          ∫ u, f (u.val * Iwasawa.diagonalUnits a * k) ∂unipotentHaar F.Carrier n
          ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar F.Carrier)
        ∂generalLinearHaar F.Carrier n :=
  IwasawaHaar.integral_generalLinearHaar_iwasawa F F.canonicalTopologicalData n f hf

/-- The normalized absolute value of the determinant of an element of `K` is one. -/
theorem normalizedAbs_det_integralK {k : Langlands.GeneralLinear (n + 1) F.Carrier}
    (hk : k ∈ integralK F n) :
    normalizedAbsoluteValue F.canonicalTopologicalData (Matrix.det k.val) = 1 :=
  normalizedAbs_det_of_mem_integralSubgroup F.canonicalTopologicalData hk

/-- The matrix integrand at `u diag(a) k`, for `k ∈ K` and a left-equivariant
`W`, is `(W(diag(a) k) |∏ a_i|^s) · (Φ(u diag(a) k) ψ_N(u))`. -/
theorem matrixIntegrand_iwasawa {ψ : UnitaryAdditiveCharacter F.Carrier}
    {W : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ}
    (hW : ∀ (u : upperUnipotent (n + 1) F.Carrier) g,
      W (u.val * g) = (standardCharacter ψ n u : ℂ) * W g)
    (Φ : MatrixTestFunction n F.Carrier) (s : ℂ) (u : upperUnipotent (n + 1) F.Carrier)
    (a : Fin (n + 1) → F.Carrierˣ) {k : Langlands.GeneralLinear (n + 1) F.Carrier}
    (hk : k ∈ integralK F n) :
    GodementJacquet.Padic.matrixIntegrand F Φ s W (u.val * Iwasawa.diagonalUnits a * k) =
      (W (Iwasawa.diagonalUnits a * k) *
        ((F.canonicalTopologicalData.normalizedAbs (∏ i, (a i : F.Carrier)) : ℝ) : ℂ) ^ s) *
      (Φ (u.val.val * Matrix.diagonal (fun i => (a i : F.Carrier)) * k.val) *
        (standardCharacter ψ n u : ℂ)) := by
  have hdet : normalizedAbsoluteValue F.canonicalTopologicalData
      (Matrix.det (Iwasawa.diagonalUnits a * k).val) =
      F.canonicalTopologicalData.normalizedAbs (∏ i, (a i : F.Carrier)) := by
    rw [Units.val_mul, Matrix.det_mul, map_mul, normalizedAbs_det_integralK F hk, mul_one,
      Iwasawa.diagonalUnits_val, Matrix.det_diagonal]
    rfl
  have hval : (u.val * Iwasawa.diagonalUnits a * k).val =
      u.val.val * Matrix.diagonal (fun i => (a i : F.Carrier)) * k.val := by
    rw [Units.val_mul, Units.val_mul, Iwasawa.diagonalUnits_val]
  simp only [GodementJacquet.Padic.matrixIntegrand, GodementJacquet.matrixIntegrand]
  rw [hval, mul_assoc u.val, determinantWeight_unipotent_mul, hW u, determinantWeight, hdet]
  ring

/-- The unipotent integral of the matrix integrand at `u diag(a) k`, for
`k ∈ K`, is `W(diag(a) k) |∏ a_i|^s` times the slice integral of `Φ(· k)`. -/
theorem integral_unipotent_matrixIntegrand {ψ : UnitaryAdditiveCharacter F.Carrier}
    {W : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ}
    (hW : ∀ (u : upperUnipotent (n + 1) F.Carrier) g,
      W (u.val * g) = (standardCharacter ψ n u : ℂ) * W g)
    (Φ : MatrixTestFunction n F.Carrier) (s : ℂ) (a : Fin (n + 1) → F.Carrierˣ)
    {k : Langlands.GeneralLinear (n + 1) F.Carrier} (hk : k ∈ integralK F n) :
    ∫ u, GodementJacquet.Padic.matrixIntegrand F Φ s W (u.val * Iwasawa.diagonalUnits a * k)
        ∂unipotentHaar F.Carrier n =
      W (Iwasawa.diagonalUnits a * k) *
        ((F.canonicalTopologicalData.normalizedAbs (∏ i, (a i : F.Carrier)) : ℝ) : ℂ) ^ s *
        WhittakerSlice.sliceIntegral F ψ (fun M => Φ (M * k.val))
          (fun i => (a i : F.Carrier)) := by
  simp_rw [matrixIntegrand_iwasawa F hW Φ s _ a hk]
  rw [integral_const_mul]
  rfl

/-- The unipotent integral of the norm of the matrix integrand at `u diag(a) k`,
for `k ∈ K`. -/
theorem lintegral_unipotent_matrixIntegrand {ψ : UnitaryAdditiveCharacter F.Carrier}
    {W : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ}
    (hW : ∀ (u : upperUnipotent (n + 1) F.Carrier) g,
      W (u.val * g) = (standardCharacter ψ n u : ℂ) * W g)
    (Φ : MatrixTestFunction n F.Carrier) (s : ℂ) (a : Fin (n + 1) → F.Carrierˣ)
    {k : Langlands.GeneralLinear (n + 1) F.Carrier} (hk : k ∈ integralK F n) :
    ∫⁻ u, ‖GodementJacquet.Padic.matrixIntegrand F Φ s W
        (u.val * Iwasawa.diagonalUnits a * k)‖ₑ ∂unipotentHaar F.Carrier n =
      ‖W (Iwasawa.diagonalUnits a * k) *
        ((F.canonicalTopologicalData.normalizedAbs (∏ i, (a i : F.Carrier)) : ℝ) : ℂ) ^ s‖ₑ *
      ∫⁻ u, ‖Φ (u.val.val * Matrix.diagonal (fun i => (a i : F.Carrier)) * k.val)‖ₑ
        ∂unipotentHaar F.Carrier n := by
  have h1 : ∀ u : upperUnipotent (n + 1) F.Carrier, ‖(standardCharacter ψ n u : ℂ)‖ₑ = 1 :=
    fun u => by rw [← ofReal_norm, norm_standardCharacter, ENNReal.ofReal_one]
  have hne : ‖W (Iwasawa.diagonalUnits a * k)‖ₑ *
      ‖((F.canonicalTopologicalData.normalizedAbs (∏ i, (a i : F.Carrier)) : ℝ) : ℂ) ^ s‖ₑ ≠
        ⊤ :=
    ENNReal.mul_ne_top enorm_ne_top enorm_ne_top
  simp_rw [matrixIntegrand_iwasawa F hW Φ s _ a hk, enorm_mul, h1, mul_one]
  rw [lintegral_const_mul' _ _ hne]

/-- The matrix integrand is right invariant under `k₀ ∈ K` fixing `Φ` and `W`. -/
theorem matrixIntegrand_mul_right {W : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ}
    (Φ : MatrixTestFunction n F.Carrier) (s : ℂ)
    {k₀ : Langlands.GeneralLinear (n + 1) F.Carrier} (hk₀ : k₀ ∈ integralK F n)
    (hΦ : ∀ M, Φ (M * k₀.val) = Φ M) (hW : ∀ g, W (g * k₀) = W g)
    (g : Langlands.GeneralLinear (n + 1) F.Carrier) :
    GodementJacquet.Padic.matrixIntegrand F Φ s W (g * k₀) =
      GodementJacquet.Padic.matrixIntegrand F Φ s W g := by
  simp only [GodementJacquet.Padic.matrixIntegrand, GodementJacquet.matrixIntegrand,
    determinantWeight]
  rw [Units.val_mul, hΦ, hW, Matrix.det_mul, map_mul, normalizedAbs_det_integralK F hk₀, mul_one]

/-- **Finite coset reduction.** For `W` as in `IsWhittakerLike` and a test
function `Φ`, there are an open subgroup `K₀ ≤ K` and a finite set `S ⊆ K` such
that the matrix integrand is right invariant under `K₀` for every `s`, and the
integral over `K` of every right-`K₀`-invariant function is the sum of its
values on `S` times the mass of `K₀`. -/
theorem IsWhittakerLike.exists_cosetSum {ψ : UnitaryAdditiveCharacter F.Carrier}
    {W : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ} (hW : IsWhittakerLike F ψ W)
    (Φ : MatrixTestFunction n F.Carrier) :
    ∃ (K₀ : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier))
      (S : Finset (Langlands.GeneralLinear (n + 1) F.Carrier)),
      (K₀ : Subgroup (Langlands.GeneralLinear (n + 1) F.Carrier)) ≤ integralK F n ∧
      (S : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) ⊆ integralK F n ∧
      (∀ s g, ∀ k₀ ∈ K₀, GodementJacquet.Padic.matrixIntegrand F Φ s W (g * k₀) =
        GodementJacquet.Padic.matrixIntegrand F Φ s W g) ∧
      (∀ f : Langlands.GeneralLinear (n + 1) F.Carrier → ℝ≥0∞,
        (∀ k ∈ integralK F n, ∀ k₀ ∈ K₀, f (k * k₀) = f k) →
        ∫⁻ x in (integralK F n : Set (Langlands.GeneralLinear (n + 1) F.Carrier)),
            f x ∂generalLinearHaar F.Carrier n =
          ∑ k ∈ S, generalLinearHaar F.Carrier n
            (K₀ : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) * f k) ∧
      (∀ f : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ,
        (∀ k ∈ integralK F n, ∀ k₀ ∈ K₀, f (k * k₀) = f k) →
        ∫ x in (integralK F n : Set (Langlands.GeneralLinear (n + 1) F.Carrier)),
            f x ∂generalLinearHaar F.Carrier n =
          ∑ k ∈ S, ((generalLinearHaar F.Carrier n).real
            (K₀ : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) : ℂ) * f k) := by
  obtain ⟨L, hL⟩ := hW.smooth
  obtain ⟨K₀, hK₀K, hK₀⟩ := CosetSum.Padic.exists_openSubgroup_rightInvariant F Φ W L hL
  obtain ⟨S, hSK, hlin, hint⟩ := CosetSum.exists_cosetSum (generalLinearHaar F.Carrier n)
    (integralK F n) (K₀ : Subgroup (Langlands.GeneralLinear (n + 1) F.Carrier))
    (CosetSum.Padic.isCompact_integralSubgroup F) K₀.isOpen hK₀K
  exact ⟨K₀, S, hK₀K, hSK, fun s g k₀ hk₀ =>
    matrixIntegrand_mul_right F Φ s (hK₀K hk₀) (hK₀ k₀ hk₀).1 (hK₀ k₀ hk₀).2 g, hlin, hint⟩

end Padic

end Langlands.GodementJacquet.WhittakerTorus
