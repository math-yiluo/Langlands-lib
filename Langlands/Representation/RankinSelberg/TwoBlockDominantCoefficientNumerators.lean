import Langlands.Representation.RankinSelberg.TwoBlockDominantNumeratorExtraction
import Langlands.Representation.RankinSelberg.TwoBlockDominantJacquetSeries
import Langlands.Representation.RankinSelberg.DualModels
import Langlands.Representation.RankinSelberg.DualWhittakerType

/-!
# Finite numerators for actual equal-rank coefficient images

The support bounds are discharged by the published support theorem for the
original and actual inverse-transpose models. The two block equations and the
lower Fourier coefficient law remain explicit premises.
-/

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
  LaurentPolynomial
open HarmonicAnalysis.BilateralLaurentSeries

universe uF uV uW

section Coefficients

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {n : ℕ}

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : MeasurableSpace (GeneralLinear (n + 1) F.Carrier) :=
  borel (GeneralLinear (n + 1) F.Carrier)
local instance : BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) :=
  borel (upperUnipotent (n + 1) F.Carrier)
local instance : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) :=
  borel (LeftUnipotentQuotient n F.Carrier)
local instance : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  (μ : Measure (LeftUnipotentQuotient n F.Carrier))
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {U : Type uW} [AddCommGroup U] [Module ℂ U]
  (π : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
  (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) U)
  (lambda : glFunctionals ψ n π) (J : glInverseFunctionals ψ n ρ)
  (f : (coefficientModel π lambda).toSubmodule)
  (f' : (coefficientModel ρ J).toSubmodule)

/-- The actual equal-rank slice series of the two dual coefficient images,
with the negated additive character and the same supplied quotient measure. -/
def equalRankDualSliceCoefficient
    (ΦD : SchwartzBruhat (Fin (n + 1) → F.Carrier)) : BilateralLaurentSeries :=
  equalRankSliceCoefficient F.canonicalTopologicalData μ (ψ.scale (-1))
    (firstDualModelMap ψ π lambda f).val (secondDualModelMap ψ ρ J f').val ΦD

/-- Actual dual coefficients have lower-bounded support. Full type of the
inverse-transpose representations is derived, not assumed. -/
theorem equalRankDualSliceCoefficient_lowerSupport
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)]
    (hμ : IsCompatible (upperUnipotent (n + 1) F.Carrier)
      (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ)
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (hρ : IsOfWhittakerType n (inverseStandardCharacter ψ n) ρ)
    (ΦD : SchwartzBruhat (Fin (n + 1) → F.Carrier)) :
    HasLowerBoundedSupport
      (equalRankDualSliceCoefficient F ψ μ π ρ lambda J f f' ΦD) := by
  have hπD : IsOfWhittakerType n (standardCharacter (ψ.scale (-1)) n)
      (inverseTransposePullback π) := by
    simpa only [standardCharacter_scale_neg_one] using
      isOfWhittakerType_inverseTransposePullback ψ π hπ
  have hρD : IsOfWhittakerType n (inverseStandardCharacter (ψ.scale (-1)) n)
      (inverseTransposePullback ρ) := by
    simpa only [inverseStandardCharacter_scale_neg_one] using
      isOfWhittakerType_inverseTransposePullback_inverse ψ ρ hρ
  exact equalRankSliceSupport F F.canonicalTopologicalData n (ψ.scale (-1)) μ hμ V U
    (inverseTransposePullback π) (inverseTransposePullback ρ) hπD hρD
    (firstDualFunctional ψ π lambda) (secondDualFunctional ψ ρ J)
    (firstDualModelMap ψ π lambda f) (secondDualModelMap ψ ρ J f') ΦD

/-- The two supplied block equations and Fourier law extract a unique finite
numerator for actual original and dual coefficient series. No support bounds
or dual full-type hypotheses are additional premises. -/
theorem twoBlock_equalRankCoefficient_numerators
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)]
    (hμ : IsCompatible (upperUnipotent (n + 1) F.Carrier)
      (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ)
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (hρ : IsOfWhittakerType n (inverseStandardCharacter ψ n) ρ)
    (Φ ΦD : SchwartzBruhat (Fin (n + 1) → F.Carrier))
    (q c₁ : ℂˣ) (d₁ : ℤ) (c₂ : ℂˣ) (d₂ : ℤ)
    (b bD : BilateralLaurentSeries) (P₁ P₁D P₂ P₂D : Polynomial ℂ) :
    let a : BilateralLaurentSeries :=
      equalRankSliceCoefficient F.canonicalTopologicalData μ ψ f.val f'.val Φ
    let aD := equalRankDualSliceCoefficient F ψ μ π ρ lambda J f f' ΦD
    Polynomial.eval₂ C (C ((q : ℂ)⁻¹) * T (-1)) P₁D • b =
        (C (c₁ : ℂ) * T d₁ * P₁.toLaurent) • a →
    Polynomial.eval₂ C (C ((q : ℂ)⁻¹) * T (-1)) P₂ • bD =
        (C (c₂ : ℂ) * T d₂ * P₂D.toLaurent) • aD →
    (∀ k : ℤ, bD (-k) = (q : ℂ) ^ (-k) * b k) →
    ∃! R : LaurentPolynomial ℂ,
      ofLaurentPolynomial R = (P₁ * P₂).toLaurent • a ∧
      ofLaurentPolynomial (laurentReflection q R) =
        (laurentReflection q
          (↑(clearedProductMultiplierUnit q c₁ d₁ c₂ d₂)⁻¹ : LaurentPolynomial ℂ) *
            (P₁D * P₂D).toLaurent) • aD := by
  intro a aD hFirst hSecond hFourier
  have ha : HasLowerBoundedSupport a :=
    equalRankSliceSupport F F.canonicalTopologicalData n ψ μ hμ V U
      π ρ hπ hρ lambda J f f' Φ
  have haD : HasLowerBoundedSupport aD :=
    equalRankDualSliceCoefficient_lowerSupport F ψ μ π ρ lambda J f f' hμ hπ hρ ΦD
  exact twoBlock_cleared_numerators q c₁ d₁ c₂ d₂ ha haD hFirst hSecond hFourier

end Coefficients

section LowerInduced

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : MeasurableSpace (GeneralLinear (t + 1) F.Carrier) :=
  borel (GeneralLinear (t + 1) F.Carrier)
local instance : BorelSpace (GeneralLinear (t + 1) F.Carrier) := ⟨rfl⟩
local instance : MeasurableSpace (upperUnipotent (t + 1) F.Carrier) :=
  borel (upperUnipotent (t + 1) F.Carrier)
local instance : BorelSpace (upperUnipotent (t + 1) F.Carrier) := ⟨rfl⟩
local instance : MeasurableSpace (LeftUnipotentQuotient t F.Carrier) :=
  borel (LeftUnipotentQuotient t F.Carrier)
local instance : BorelSpace (LeftUnipotentQuotient t F.Carrier) := ⟨rfl⟩

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
  (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
  [hinv : Measure.IsMulRightInvariant (unipotentHaar F.Carrier t)]
  (μ : Measure (LeftUnipotentQuotient t F.Carrier))
  (hμ : IsCompatible (upperUnipotent (t + 1) F.Carrier)
    (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) μ)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear (t + 1) F.Carrier) V)
  (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
  (lambda : glFunctionals ψ t π)
  (J : glInverseFunctionals ψ t (TwoBlockJacquet.inducedRep F h σ))
  (f : (coefficientModel π lambda).toSubmodule)
  (f' : (coefficientModel (TwoBlockJacquet.inducedRep F h σ) J).toSubmodule)
  (Φ ΦD : SchwartzBruhat (Fin (t + 1) → F.Carrier))

include hσ hμ hπ hinv

/-- Both actual coefficient series for a lower induced model have
lower-bounded support. The full type of that induction and its dual is
derived from the full types of the supplied blocks. -/
theorem lowerInducedCoefficient_support :
    HasLowerBoundedSupport
        (equalRankSliceCoefficient F.canonicalTopologicalData μ ψ f.val f'.val Φ) ∧
      HasLowerBoundedSupport
        (equalRankDualSliceCoefficient F ψ μ π
          (TwoBlockJacquet.inducedRep F h σ) lambda J f f' ΦD) := by
  have hρ := lowerInduced_inverseWhittakerType F h ψ σ hσ
  exact ⟨equalRankSliceSupport F F.canonicalTopologicalData t ψ μ hμ V
      (TwoBlockJacquet.Sections F h σ) π (TwoBlockJacquet.inducedRep F h σ)
      hπ hρ lambda J f f' Φ,
    equalRankDualSliceCoefficient_lowerSupport F ψ μ π
      (TwoBlockJacquet.inducedRep F h σ) lambda J f f' hμ hπ hρ ΦD⟩

/-- Actual two-block lower induction needs no induced-type or support
premise for numerator extraction. The block equations and Fourier law
remain to be proved by the analytic part of the argument. -/
theorem twoBlock_lowerInducedCoefficient_numerators
    (q c₁ : ℂˣ) (d₁ : ℤ) (c₂ : ℂˣ) (d₂ : ℤ)
    (b bD : BilateralLaurentSeries) (P₁ P₁D P₂ P₂D : Polynomial ℂ) :
    let a : BilateralLaurentSeries :=
      equalRankSliceCoefficient F.canonicalTopologicalData μ ψ f.val f'.val Φ
    let aD := equalRankDualSliceCoefficient F ψ μ π
      (TwoBlockJacquet.inducedRep F h σ) lambda J f f' ΦD
    Polynomial.eval₂ C (C ((q : ℂ)⁻¹) * T (-1)) P₁D • b =
        (C (c₁ : ℂ) * T d₁ * P₁.toLaurent) • a →
    Polynomial.eval₂ C (C ((q : ℂ)⁻¹) * T (-1)) P₂ • bD =
        (C (c₂ : ℂ) * T d₂ * P₂D.toLaurent) • aD →
    (∀ k : ℤ, bD (-k) = (q : ℂ) ^ (-k) * b k) →
    ∃! R : LaurentPolynomial ℂ,
      ofLaurentPolynomial R = (P₁ * P₂).toLaurent • a ∧
      ofLaurentPolynomial (laurentReflection q R) =
        (laurentReflection q
          (↑(clearedProductMultiplierUnit q c₁ d₁ c₂ d₂)⁻¹ : LaurentPolynomial ℂ) *
            (P₁D * P₂D).toLaurent) • aD :=
  twoBlock_equalRankCoefficient_numerators F ψ μ π
    (TwoBlockJacquet.inducedRep F h σ) lambda J f f' hμ hπ
    (lowerInduced_inverseWhittakerType F h ψ σ hσ) Φ ΦD
    q c₁ d₁ c₂ d₂ b bD P₁ P₁D P₂ P₂D

end LowerInduced

end Langlands.RankinSelberg.DominantRankTransport
