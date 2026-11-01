import Langlands.Representation.RankinSelberg.TwoBlockDominantStrictCoefficients
import Langlands.Representation.RankinSelberg.TwoBlockDominantDualSlices
import Langlands.Representation.RankinSelberg.TwoBlockDominantNumeratorExtraction
import Langlands.Representation.RankinSelberg.TwoBlockDominantDualMatrixProof

/-!
# Finite numerators for actual strictly dominant Jacquet coefficients

Support and the actual lower Fourier coefficient law are discharged. The two
first-block Laurent identities remain explicit premises.
-/

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
  LaurentPolynomial TwoBlockJacquet TwoBlockDominantRectangular
open HarmonicAnalysis.BilateralLaurentSeries

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance strictNumeratorTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance strictNumeratorValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance strictNumeratorLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance strictNumeratorT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance strictNumeratorMeasurable : MeasurableSpace F.Carrier := borel _
local instance strictNumeratorBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance strictNumeratorQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance strictNumeratorQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩

section Support

variable {n r j k : ℕ}

/-- Actual dual coefficient, with the source's right Weyl translation and
exchanged complementary rectangle sizes. -/
def strictDualSliceCoefficient (hr : r = n + (j + k + 1))
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (μ : Measure (LeftUnipotentQuotient n F.Carrier))
    (ν : AdditiveHaarMeasure F.Carrier)
    (Wtest : WhittakerFunctions ψ r)
    (WjacD : InverseWhittakerFunctions (ψ.scale (-1)) n) :
    BilateralLaurentSeries :=
  strictSliceCoefficient F (by omega : r = n + (k + j + 1))
    (ψ.scale (-1)) μ ν (reversedDualTest hr ψ Wtest) WjacD

/-- The prescribed translated dual test lies in the actual smooth
inverse-transpose model, so its coefficients also have a finite negative tail. -/
theorem strictDualSliceCoefficient_lowerSupport
    (hr : r = n + (j + k + 1))
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (μ : Measure (LeftUnipotentQuotient n F.Carrier))
    (ν : AdditiveHaarMeasure F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hπ : IsSmooth π) (lambda : glFunctionals ψ r π)
    (f : (coefficientModel π lambda).toSubmodule)
    (WjacD : InverseWhittakerFunctions (ψ.scale (-1)) n) :
    HasLowerBoundedSupport
      (strictDualSliceCoefficient F hr ψ μ ν f.val WjacD) := by
  exact strictSliceCoefficient_lowerSupport F (by omega : r = n + (k + j + 1))
    (ψ.scale (-1)) μ ν (inverseTransposePullback π)
    (Whittaker.inverseTransposePullback_isSmooth π hπ)
    (firstDualFunctional ψ π lambda)
    (translatedFirstDualModelEquiv ψ π lambda (rightWeyl hr) f) WjacD

end Support

/-- The canonical nonzero residue cardinality, as a complex unit. -/
def strictResidueCardinalityUnit : ℂˣ :=
  Units.mk0 (F.canonicalTopologicalData.residueCardinality : ℂ) (by
    have hq : F.canonicalTopologicalData.residueCardinality ≠ 0 :=
      ne_of_gt (lt_trans Nat.zero_lt_one
        F.canonicalTopologicalData.residueCardinality_gt_one)
    exact_mod_cast hq)

@[simp]
theorem coe_strictResidueCardinalityUnit :
    (strictResidueCardinalityUnit F : ℂ) =
      (F.canonicalTopologicalData.residueCardinality : ℂ) := rfl

section Induced

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [hadd : ∀ i, AddCommGroup (W i)]
  [hmod : ∀ i, Module ℂ (W i)]

local instance strictNumeratorReverseAdd : ∀ i : Fin 2, AddCommGroup (W i.rev) :=
  fun i => hadd i.rev
local instance strictNumeratorReverseModule : ∀ i : Fin 2, Module ℂ (W i.rev) :=
  fun i => hmod i.rev
local instance strictNumeratorGLTopology :
    IsTopologicalGroup (GeneralLinear (t + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
local instance strictNumeratorGLMeasurable :
    MeasurableSpace (GeneralLinear (t + 1) F.Carrier) := borel _
local instance strictNumeratorGLBorel :
    BorelSpace (GeneralLinear (t + 1) F.Carrier) := ⟨rfl⟩
local instance strictNumeratorUnipotentMeasurable :
    MeasurableSpace (upperUnipotent (t + 1) F.Carrier) := borel _
local instance strictNumeratorUnipotentBorel :
    BorelSpace (upperUnipotent (t + 1) F.Carrier) := ⟨rfl⟩
local instance strictNumeratorLowerMeasurable :
    MeasurableSpace (TwoBlockLowerUnipotentQuotient.LowerQuotient h F.Carrier) :=
  borel _
local instance strictNumeratorLowerBorel :
    BorelSpace (TwoBlockLowerUnipotentQuotient.LowerQuotient h F.Carrier) := ⟨rfl⟩

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
  (hσ : ∀ i, IsSmooth (σ i))
  (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
  {r j k : ℕ} (hr : r = t + (j + k + 1))
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
  (hπ : IsSmooth π) (lambda : glFunctionals ψ r π)
  (J : glInverseFunctionals ψ t (inducedRep F h σ))
  (JD : glInverseFunctionals (ψ.scale (-1)) t
    (inducedRep F (TwoBlockLowerUnipotentQuotient.reverse_sum h)
      (fun i => inverseTransposePullback (σ i.rev))))
  (μ : Measure (LeftUnipotentQuotient t F.Carrier))
  (ν : AdditiveHaarMeasure F.Carrier)
  (hN : Measure.IsMulRightInvariant (unipotentHaar F.Carrier t))
  (hμ : IsCompatible (upperUnipotent (t + 1) F.Carrier)
    (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) μ)
  (f : Sections F h σ) (Wtest : (coefficientModel π lambda).toSubmodule)

include hπ hN hμ

/-- The actual original and reversed-dual induced coefficients have a unique
finite numerator, conditional only on the two displayed first-block equations.
The support bounds, residue scalar and actual Fourier law are derived. -/
theorem twoBlock_strictInducedCoefficient_numerators
    (c₁ : ℂˣ) (d₁ : ℤ) (c₂ : ℂˣ) (d₂ : ℤ)
    (P₁ P₁D P₂ P₂D : Polynomial ℂ) :
    let q := strictResidueCardinalityUnit F
    let a := strictSliceCoefficient F hr ψ μ ν Wtest.val
      (modelMap (inducedRep F h σ) J f).val
    let aD := strictDualSliceCoefficient F hr ψ μ ν Wtest.val
      (modelMap
        (inducedRep F (TwoBlockLowerUnipotentQuotient.reverse_sum h)
          (fun i => inverseTransposePullback (σ i.rev))) JD
        (reversedDualSectionEquiv F h σ hσ f)).val
    let b : BilateralLaurentSeries :=
      kernelSliceCoefficient ν ell f Wtest.val μ hr
    let bD : BilateralLaurentSeries :=
      reversedDualSliceCoefficient F h σ hσ ψ ell hr f Wtest.val ν μ
    Polynomial.eval₂ C (C ((q : ℂ)⁻¹) * T (-1)) P₁D • b =
        (C (c₁ : ℂ) * T d₁ * P₁.toLaurent) • a →
    Polynomial.eval₂ C (C ((q : ℂ)⁻¹) * T (-1)) P₂ • bD =
        (C (c₂ : ℂ) * T d₂ * P₂D.toLaurent) • aD →
    ∃! R : LaurentPolynomial ℂ,
      ofLaurentPolynomial R = (P₁ * P₂).toLaurent • a ∧
      ofLaurentPolynomial (laurentReflection q R) =
        (laurentReflection q
          (↑(clearedProductMultiplierUnit q c₁ d₁ c₂ d₂)⁻¹ : LaurentPolynomial ℂ) *
            (P₁D * P₂D).toLaurent) • aD := by
  intro q a aD b bD hFirst hSecond
  have ha : HasLowerBoundedSupport a :=
    strictSliceCoefficient_lowerSupport F hr ψ μ ν π hπ lambda Wtest
      (modelMap (inducedRep F h σ) J f).val
  have haD : HasLowerBoundedSupport aD :=
    strictDualSliceCoefficient_lowerSupport F hr ψ μ ν π hπ lambda Wtest
      (modelMap
        (inducedRep F (TwoBlockLowerUnipotentQuotient.reverse_sum h)
          (fun i => inverseTransposePullback (σ i.rev))) JD
        (reversedDualSectionEquiv F h σ hσ f)).val
  have hFourier (d : ℤ) : bD (-d) = (q : ℂ) ^ (-d) * b d := by
    dsimp only [bD, b, q]
    simpa only [coe_strictResidueCardinalityUnit, neg_neg] using
      reversedDualSliceCoefficient_eq F h σ hσ ψ ell hr f Wtest.val ν μ
        hN hμ twoBlockDominantDualMatrix (-d)
  exact twoBlock_cleared_numerators q c₁ d₁ c₂ d₂ ha haD hFirst hSecond hFourier

end Induced

end Langlands.RankinSelberg.DominantRankTransport
