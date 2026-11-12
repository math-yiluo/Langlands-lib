import Langlands.HarmonicAnalysis.Distribution.RenardCompletionStatements
import Langlands.Algebra.NondegenerateModuleCenter

/-! # Renard II.3.13: the actual categorical center and invariant distributions -/

noncomputable section

open MeasureTheory Langlands.Algebra

namespace Langlands.HarmonicAnalysis.Distribution.RenardCenter

universe uG uM

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- Equation (II.3.13.2) uses scalar test/distribution convolution, with
actual test witnesses, rather than convolution of the two bare densities. -/
def TraceCondition (T : Distribution G) : Prop :=
  ∀ (f : SchwartzBruhat G) (h : Hecke.HeckeAlgebra μ),
    ∃ fh hf : SchwartzBruhat G,
      (fh : G → ℂ) = rightConvolveTest f (heckeDistribution μ h) ∧
      (hf : G → ℂ) = leftConvolveTest (heckeDistribution μ h) f ∧
      T fh = T hf

/-- The source's equality for Dirac translations, expressed on actual tests. -/
def TranslationCondition (T : Distribution G) : Prop :=
  ∀ (g : G) (f : SchwartzBruhat G),
    T (Hecke.TestFunction.leftTranslate g f) =
      T (Hecke.TestFunction.rightTranslate g⁻¹ f)

/-- Equation (II.3.13.3), including its four local-idempotent requirements
and the actual compact convolution e_K*δ_g*e_K. -/
def SandwichTraceCondition (T : Distribution G) : Prop :=
  ∀ (f : SchwartzBruhat G) (g : G)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)),
    let e := compactSubgroupHaar K.toSubgroup hK
    leftConvolveTest (e : Distribution G) f = (f : G → ℂ) →
    rightConvolveTest f (e : Distribution G) = (f : G → ℂ) →
    leftConvolveTest (e : Distribution G) (Hecke.TestFunction.leftTranslate g f) =
        (Hecke.TestFunction.leftTranslate g f : G → ℂ) →
    rightConvolveTest (Hecke.TestFunction.rightTranslate g⁻¹ f) (e : Distribution G) =
        (Hecke.TestFunction.rightTranslate g⁻¹ f : G → ℂ) →
    ∃ l r : SchwartzBruhat G,
      (l : G → ℂ) =
        leftConvolveTest (convolution (convolution e (compactDirac g)) e : Distribution G) f ∧
      (r : G → ℂ) =
        rightConvolveTest f (convolution (convolution e (compactDirac g)) e : Distribution G) ∧
      T l = T r

/-- The center of the right product algebra is the Hecke commutant; its
members are precisely the conjugation-invariant right-essentially-compact
distributions, and are automatically two-sided essentially compact. -/
def CentralitySpecification
    (p : rightEssentiallyCompact μ →ₗ[ℂ]
      rightEssentiallyCompact μ →ₗ[ℂ] rightEssentiallyCompact μ) : Prop :=
  ∀ T : rightEssentiallyCompact μ,
    ((∀ U : rightEssentiallyCompact μ, p T U = p U T) ↔
      ∀ h : Hecke.HeckeAlgebra μ,
        rightHeckeConvolution μ (T : Distribution G) h =
          leftHeckeConvolution μ h (T : Distribution G)) ∧
    ((∀ h : Hecke.HeckeAlgebra μ,
        rightHeckeConvolution μ (T : Distribution G) h =
          leftHeckeConvolution μ h (T : Distribution G)) ↔
      IsConjugationInvariant (T : Distribution G)) ∧
    (IsConjugationInvariant (T : Distribution G) →
      (T : Distribution G) ∈ essentiallyCompact μ)

/-- The actual categorical-center comparison, explicitly tied to the
published compatible-family action on every nondegenerate original module.
The module universe contains the Hecke algebra universe. -/
def CategoricalComparisonSpecification
    (hA : IsIdempotented (Hecke.HeckeAlgebra μ))
    (p : essentiallyCompact μ →ₗ[ℂ]
      essentiallyCompact μ →ₗ[ℂ] essentiallyCompact μ)
    (E : rightEssentiallyCompact μ ≃+
      IdempotentedRingRightLimit (Hecke.HeckeAlgebra μ))
    (C : NondegenerateModuleCenter.{uG, max uG uM} (Hecke.HeckeAlgebra μ) ≃
      {T : essentiallyCompact μ // IsConjugationInvariant (T : Distribution G)}) : Prop :=
  letI := NondegenerateModuleCenter.ring.{uG, max uG uM} (Hecke.HeckeAlgebra μ)
  (∀ z w,
    ((C (z + w)).val : Distribution G) =
      ((C z).val : Distribution G) + ((C w).val : Distribution G)) ∧
  (∀ z w, (C (z * w)).val = p (C z).val (C w).val) ∧
  ((C 1).val : Distribution G) = dirac 1 ∧
  ∀ z,
    ∃ T : rightEssentiallyCompact μ,
      (T : Distribution G) = ((C z).val : Distribution G) ∧
      ∃ x : NondegenerateModuleCenter.Commutant hA,
        x.val = E T ∧
        NondegenerateModuleCenter.fromCommutantRingHom.{uG, max uG uM} hA x = z

/-- The trace, translation and compact-open sandwich criteria in the
Corollary's proof, for the original full algebraic distributions. -/
def CriteriaStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (T : Distribution G),
    (IsConjugationInvariant T ↔ TranslationCondition T) ∧
    (IsConjugationInvariant T ↔ TraceCondition μ T) ∧
    (IsConjugationInvariant T ↔ SandwichTraceCondition T)

/-- II.3.13 Corollary, on the actual natural-endomorphism center, with all
distribution products and the actual completion comparison supplied. -/
def CategoricalCenterStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure],
    ∃ (hA : IsIdempotented (Hecke.HeckeAlgebra μ))
      (pr : rightEssentiallyCompact μ →ₗ[ℂ]
        rightEssentiallyCompact μ →ₗ[ℂ] rightEssentiallyCompact μ)
      (pl : leftEssentiallyCompact μ →ₗ[ℂ]
        leftEssentiallyCompact μ →ₗ[ℂ] leftEssentiallyCompact μ)
      (p : essentiallyCompact μ →ₗ[ℂ]
        essentiallyCompact μ →ₗ[ℂ] essentiallyCompact μ)
      (E : rightEssentiallyCompact μ ≃+
        IdempotentedRingRightLimit (Hecke.HeckeAlgebra μ)),
      RenardEssentialProducts.RightProductSpecification μ pr ∧
      RenardEssentialProducts.LeftProductSpecification μ pl ∧
      RenardEssentialProducts.TwoSidedProductSpecification μ pr pl p ∧
      RenardCompletion.ComparisonSpecification μ hA pr E ∧
      CentralitySpecification μ pr ∧
      ∃ C : NondegenerateModuleCenter.{uG, max uG uM} (Hecke.HeckeAlgebra μ) ≃
          {T : essentiallyCompact μ // IsConjugationInvariant (T : Distribution G)},
        CategoricalComparisonSpecification μ hA p E C

def Statements : Prop :=
  CriteriaStatement.{uG} ∧ CategoricalCenterStatement.{uG, uM}

end Langlands.HarmonicAnalysis.Distribution.RenardCenter
