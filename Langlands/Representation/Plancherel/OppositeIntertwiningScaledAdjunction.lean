import Langlands.Representation.Plancherel.OppositeIntertwiningHermitianAdjunction
import Langlands.Representation.Plancherel.ScaledIwasawaExchange

/-! # Hermitian adjunction with arbitrary compact Iwasawa data -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal ComplexConjugate

namespace Langlands.Plancherel.OppositeIntertwiningHermitianAdjunction

open Aubert.General Induction StandardIntertwining

universe uG uV

section Scale

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [MeasurableSpace G] {M U U' : Subgroup G}
  [MeasurableSpace M] [MeasurableSpace U] [MeasurableSpace U']

/-- The positive real scalar comparing the two original Iwasawa normalizations
in the Hermitian adjunction. -/
def hermitianAdjunctionScale (K : OpenSubgroup G)
    (μM : Measure M) (μU : Measure U) (μU' : Measure U') : ℝ :=
  (LeviInvariantIwasawaExchange.iwasawaExchangeRatio K μM μU μU').toReal

end Scale

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {P M U P' U' : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (h' : IsSemidirectDecomposition P' M U') (hU' : IsClosed (U' : Set G))
  {A : SmoothRep.{0, uG, uV} ℂ M} (b : InvariantPositiveForm A.representation)
  {χ₁ χ₂ : M →* ℂˣ} {hχ₁ : IsOpen (χ₁.ker : Set M)}
  {hχ₂ : IsOpen (χ₂.ker : Set M)}

/-- The actual K-integral Hermitian adjunction up to the exact real normalization
factor, without assuming either compact intersection splits. -/
theorem setIntegral_inner_eq_scaled [MeasurableSpace M] [BorelSpace M]
    [MeasurableSpace U] [BorelSpace U] [MeasurableSpace U'] [BorelSpace U']
    [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')]
    [MeasurableSpace (U'.subgroupOf U)] [BorelSpace (U'.subgroupOf U)]
    [MeasurableSpace (QuotientSpace (U := U) U')] [BorelSpace (QuotientSpace (U := U) U')]
    [MeasurableSpace (QuotientSpace (U := U') U)] [BorelSpace (QuotientSpace (U := U') U)]
    (hbot : U ⊓ U' = ⊥) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
    (hP'K : ∀ g : G, ∃ p : P', ∃ k : K, g = (p : G) * (k : G))
    (hP : IsClosed (P : Set G)) (hP' : IsClosed (P' : Set G))
    (hr : Continuous h.projection) (hr' : Continuous h'.projection)
    (hrec : ∀ m : M, HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer m *
      HaarModulus.closedRestrictCharacter U' hU' M h'.levi_le_normalizer m = 1)
    (hχ : ∀ m : M, starRingEnd ℂ (χ₁ m : ℂ) * (χ₂ m : ℂ) = 1)
    {μM : Measure M} [SFinite μM] [μM.IsHaarMeasure] [μM.IsMulRightInvariant]
    {μU : Measure U} [IsHaarMeasure μU] [μU.Regular] [SFinite μU]
    {μU' : Measure U'} [IsHaarMeasure μU'] [μU'.Regular] [SFinite μU']
    {μI : Measure (U.subgroupOf U')} [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
    (hμI : μI Set.univ = 1)
    {μI' : Measure (U'.subgroupOf U)} [IsHaarMeasure μI'] [μI'.Regular] [IsMulRightInvariant μI']
    (hμI' : μI' Set.univ = 1)
    {ν : Measure (QuotientSpace (U := U) U')}
    (hν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI ν)
    {ν' : Measure (QuotientSpace (U := U') U)}
    (hν' : QuotientIntegration.IsCompatible (U'.subgroupOf U) μU μI' ν')
    {μ : Measure G} [μ.IsMulLeftInvariant] [SFinite μ] [IsFiniteMeasureOnCompacts μ]
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj (A.twist χ₁ hχ₁))
    (f' : (DynamicNormalization.leviTwistedInductionFunctor h' hU').obj (A.twist χ₂ hχ₂))
    {Jf Jf' : G → A} (hJ : HasIntegral h hU U' (A.twist χ₁ hχ₁) ν f Jf)
    (hJ' : HasIntegral h' hU' U (A.twist χ₂ hχ₂) ν' f' Jf') :
    ∫ x in (K : Set G), b.inner (Jf x)
        (eval P' (leviInflatedInducingRepresentation h' hU' (A.twist χ₂ hχ₂)) f' x) ∂μ =
      hermitianAdjunctionScale K μM μU μU' •
      ∫ x in (K : Set G), b.inner
        (eval P (leviInflatedInducingRepresentation h hU (A.twist χ₁ hχ₁)) f x) (Jf' x) ∂μ := by
  have : SecondCountableTopology U := TopologicalSpace.Subtype.secondCountableTopology _
  have : SecondCountableTopology U' := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨L, hL⟩ := exists_hermitianIntegrand_mul_right h hU h' hU' b f f'
  have hc := LeviInvariantIwasawaExchange.continuous_of_mul_right_invariant L.isOpen
    (hermitianIntegrand h hU h' hU' b f f') hL
  have hfw := forward_inner_eq h hU h' hU' b hbot hμI hν f f' hJ
  have hrv := reverse_inner_eq h hU h' hU' b hbot hμI' hν' f f' hJ'
  have hint := LeviInvariantIwasawaExchange.integrable_iwasawaCoordinates (W := U')
    (K := (K : Subgroup G)) (μ := μ) (μW := μU') L.isOpen K.isOpen hK
    (hermitianIntegrand h hU h' hU' b f f') hL (fun k _ => (hfw k).1)
  have hex := (LeviInvariantIwasawaExchange.integral_exchange_scaled
    (μ := μ) h h' K μM μU μU' hP hP' hK hr hr'
    (exists_levi_unipotent_compact h K hPK)
    (exists_levi_unipotent_compact h' K hP'K)
    (hermitianIntegrand h hU h' hU' b f f') hc.measurable
    (hermitianIntegrand_levi_mul h hU h' hU' b hrec hχ f f') hint).2
  calc _ = ∫ k in (K : Set G), ∫ v : U', hermitianIntegrand h hU h' hU' b f f' ((v : G) * k)
          ∂μU' ∂μ :=
        setIntegral_congr_fun K.isOpen.measurableSet fun k _ => (hfw k).2
    _ = hermitianAdjunctionScale K μM μU μU' •
        (∫ k in (K : Set G), ∫ u : U, hermitianIntegrand h hU h' hU' b f f' ((u : G) * k)
          ∂μU ∂μ) := hex
    _ = _ := congrArg (fun z : ℂ => hermitianAdjunctionScale K μM μU μU' • z)
      (setIntegral_congr_fun K.isOpen.measurableSet fun k _ => (hrv k).2).symm


end Langlands.Plancherel.OppositeIntertwiningHermitianAdjunction
