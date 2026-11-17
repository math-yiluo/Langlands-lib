import Langlands.Representation.Plancherel.OppositeIntertwiningScaledAdjunction
import Langlands.Representation.Plancherel.StandardIntertwiningScalarBounds
import Langlands.Representation.Induction.CompactLocalSection
import Langlands.Representation.Twist.AdmissibilityProof

/-! # Conjugate-inverse convergence from forward convergence -/

noncomputable section


open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal ComplexConjugate

namespace Langlands.Plancherel.OppositeIntertwiningHermitianAdjunction

open Aubert.General Induction StandardIntertwining

universe uG uV

section Slice

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  {U : Subgroup G} [MeasurableSpace U]
  {μ : Measure G} [μ.IsHaarMeasure] [SFinite μ] {μU : Measure U} [SFinite μU]

omit [IsTopologicalGroup G] in
/-- An open right stabilizer upgrades almost-everywhere slice integrability
on `K × U` to integrability of the slice at the identity. -/
theorem integrable_at_one_of_iwasawaCoordinates
    (K L : OpenSubgroup G) (Θ : G → ℂ)
    (hright : ∀ g : G, ∀ k ∈ L, Θ (g * k) = Θ g)
    (hint : Integrable (fun p : G × U => Θ ((p.2 : G) * p.1))
      ((μ.restrict (K : Set G)).prod μU)) :
    Integrable (fun u : U => Θ (u : G)) μU := by
  let J := L ⊓ K
  have hJ : (μ.restrict (K : Set G)) (J : Set G) ≠ 0 := by
    rw [Measure.restrict_apply J.isOpen.measurableSet,
      Set.inter_eq_left.mpr (show (J : Set G) ⊆ (K : Set G) from fun _ hh => hh.2)]
    exact J.isOpen.measure_ne_zero μ ⟨1, J.one_mem⟩
  obtain ⟨k, hk, hintk⟩ := exists_mem_of_measure_ne_zero_of_ae hJ
    (ae_restrict_of_ae hint.prod_right_ae)
  apply hintk.congr
  exact ae_of_all _ fun u => hright (u : G) k hk.1

end Slice

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {P M U P' U' : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (h' : IsSemidirectDecomposition P' M U') (hU' : IsClosed (U' : Set G))
  {A : SmoothRep.{0, uG, uV} ℂ M} (b : InvariantPositiveForm A.representation)
  {χ₁ χ₂ : M →* ℂˣ} {hχ₁ : IsOpen (χ₁.ker : Set M)}
  {hχ₂ : IsOpen (χ₂.ker : Set M)}

omit [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
private theorem exists_leviInflatedSection
    (hr : Continuous h.projection) (B : SmoothRep.{0, uG, uV} ℂ M) (v : B) :
    ∃ f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj B,
      eval P (leviInflatedInducingRepresentation h hU B) f 1 = v := by
  let σ := leviInflatedInducingRepresentation h hU B
  have hσ : IsSmooth σ :=
    isSmooth_comp h.projection hr ((isSmooth_twist_iff _ _
      (HaarModulus.isOpen_ker_closedHalfCharacter U hU M h.levi_le_normalizer)).mpr B.isSmooth)
  exact ⟨(compactLocalSection P σ hσ 1 v Set.univ isOpen_univ (Set.mem_univ _)).val,
    compactLocalSection_apply P σ hσ 1 v Set.univ isOpen_univ (Set.mem_univ _)⟩

include b in
/-- Full forward convergence forces full scalar convergence in the reverse
conjugate-inverse direction for an admissible coefficient representation. -/
theorem scalarDomain_eq_top_of_forward
    [MeasurableSpace M] [BorelSpace M]
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
    (hcofinal : ∀ J : OpenSubgroup M, ∃ L : OpenSubgroup M, IsCompact (L : Set M) ∧ L ≤ J)
    (hA : A.IsAdmissible)
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
    {μ : Measure G} [μ.IsHaarMeasure] [SFinite μ]
    (hfull : domain h hU U' (A.twist χ₁ hχ₁) ν = ⊤) :
    scalarDomain h' hU' U (A.twist χ₂ hχ₂) ν' = ⊤ := by
  have : SecondCountableTopology U := TopologicalSpace.Subtype.secondCountableTopology _
  have : SecondCountableTopology U' := TopologicalSpace.Subtype.secondCountableTopology _
  apply (scalarDomain_eq_top_iff_integrable_at_one h' hU' U (A.twist χ₂ hχ₂) ν').mpr
  intro f' ℓ
  let ℓ₀ : SmoothDual A.representation :=
    smoothContragredientTwistEquiv χ₂ A.representation hχ₂ ℓ
  obtain ⟨v, hv⟩ := b.toSmoothDual_surjective hcofinal hA ℓ₀
  have hv' (w : A) : b.inner v w = ℓ.val w :=
    congrArg (fun η : SmoothDual A.representation => η.val w) hv
  obtain ⟨f, he⟩ := exists_leviInflatedSection h hU hr (A.twist χ₁ hχ₁) v
  have hf : f ∈ domain h hU U' (A.twist χ₁ hχ₁) ν := by rw [hfull]; trivial
  obtain ⟨Jf, hJ⟩ := (mem_domain h hU U' (A.twist χ₁ hχ₁) ν f).mp hf
  obtain ⟨L, hL⟩ := exists_hermitianIntegrand_mul_right h hU h' hU' b f f'
  have hc := LeviInvariantIwasawaExchange.continuous_of_mul_right_invariant L.isOpen
    (hermitianIntegrand h hU h' hU' b f f') hL
  have hfw := forward_inner_eq h hU h' hU' b hbot hμI hν f f' hJ
  have hint := LeviInvariantIwasawaExchange.integrable_iwasawaCoordinates (W := U')
    (K := (K : Subgroup G)) (μ := μ) (μW := μU') L.isOpen K.isOpen hK
    (hermitianIntegrand h hU h' hU' b f f') hL (fun k _ => (hfw k).1)
  have hintU := (LeviInvariantIwasawaExchange.integral_exchange_scaled
    (μ := μ) h h' K μM μU μU' hP hP' hK hr hr'
    (exists_levi_unipotent_compact h K hPK)
    (exists_levi_unipotent_compact h' K hP'K)
    (hermitianIntegrand h hU h' hU' b f f') hc.measurable
    (hermitianIntegrand_levi_mul h hU h' hU' b hrec hχ f f') hint).1
  have hs := integrable_at_one_of_iwasawaCoordinates K L
    (hermitianIntegrand h hU h' hU' b f f') hL hintU
  have hpoint (u : U) : hermitianIntegrand h hU h' hU' b f f' (u : G) =
      ℓ.val (integrand h' hU' U (A.twist χ₂ hχ₂) 1 f' (Quotient.mk _ u)) := by
    rw [integrand_mk, mul_one]
    unfold hermitianIntegrand
    have hfu := source_unipotent_invariant h hU (A.twist χ₁ hχ₁) f u 1
    rw [mul_one] at hfu
    rw [hfu, he]
    exact hv' _
  have hi : Integrable (fun u : U =>
      ℓ.val (integrand h' hU' U (A.twist χ₂ hχ₂) 1 f' (Quotient.mk _ u))) μU :=
    hs.congr (ae_of_all _ hpoint)
  have : IsFiniteMeasure μI' := ⟨by rw [hμI']; exact ENNReal.one_lt_top⟩
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  exact (integrable_trivialQuotient_iff (U'.subgroupOf U)
    (subgroupOf_eq_one ((inf_comm _ _).trans hbot))
    (hU'.preimage continuous_subtype_val) hμI' hν' _).mpr hi

include b in
/-- Admissibility turns the reverse scalar convergence into the whole actual
weak-integral domain. -/
theorem domain_eq_top_of_forward
    [MeasurableSpace M] [BorelSpace M]
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
    (hcofinal : ∀ J : OpenSubgroup M, ∃ L : OpenSubgroup M, IsCompact (L : Set M) ∧ L ≤ J)
    (hA : A.IsAdmissible)
    {μM : Measure M} [SFinite μM] [μM.IsHaarMeasure] [μM.IsMulRightInvariant]
    {μU : Measure U} [IsHaarMeasure μU] [μU.Regular] [SFinite μU] [μU.IsMulRightInvariant]
    {μU' : Measure U'} [IsHaarMeasure μU'] [μU'.Regular] [SFinite μU']
    {μI : Measure (U.subgroupOf U')} [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
    (hμI : μI Set.univ = 1)
    {μI' : Measure (U'.subgroupOf U)} [IsHaarMeasure μI'] [μI'.Regular] [IsMulRightInvariant μI']
    (hμI' : μI' Set.univ = 1)
    {ν : Measure (QuotientSpace (U := U) U')}
    (hν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI ν)
    {ν' : Measure (QuotientSpace (U := U') U)}
    (hν' : QuotientIntegration.IsCompatible (U'.subgroupOf U) μU μI' ν')
    {μ : Measure G} [μ.IsHaarMeasure] [SFinite μ]
    (hM : IsClosed (M : Set G))
    (hsq : SquaredModulusCompatibility h' hU' h hU)
    (hfull : domain h hU U' (A.twist χ₁ hχ₁) ν = ⊤) :
    domain h' hU' U (A.twist χ₂ hχ₂) ν' = ⊤ := by
  have hs := scalarDomain_eq_top_of_forward h hU h' hU' b (hχ₂ := hχ₂) hbot K hK hPK hP'K hP hP' hr hr' hrec hχ
    hcofinal hA (μM := μM) hμI hμI' hν hν' (μ := μ) hfull
  have hA' : (A.twist χ₂ hχ₂).IsAdmissible :=
    (isAdmissible_twist_iff χ₂ A.representation hχ₂).mpr hA
  rw [scalarDomain_eq_domain h' hU' U (A.twist χ₂ hχ₂) ν'
    h hU μU μI' hν' hM hA' hsq] at hs
  exact hs

/-- The actual reverse convergence domain is the entire source, expressed as
the identity linear equivalence, constructed from forward convergence. -/
def reverseDomainEquiv
    [MeasurableSpace M] [BorelSpace M]
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
    (hcofinal : ∀ J : OpenSubgroup M, ∃ L : OpenSubgroup M, IsCompact (L : Set M) ∧ L ≤ J)
    (hA : A.IsAdmissible)
    {μM : Measure M} [SFinite μM] [μM.IsHaarMeasure] [μM.IsMulRightInvariant]
    {μU : Measure U} [IsHaarMeasure μU] [μU.Regular] [SFinite μU] [μU.IsMulRightInvariant]
    {μU' : Measure U'} [IsHaarMeasure μU'] [μU'.Regular] [SFinite μU']
    {μI : Measure (U.subgroupOf U')} [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
    (hμI : μI Set.univ = 1)
    {μI' : Measure (U'.subgroupOf U)} [IsHaarMeasure μI'] [μI'.Regular] [IsMulRightInvariant μI']
    (hμI' : μI' Set.univ = 1)
    {ν : Measure (QuotientSpace (U := U) U')}
    (hν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI ν)
    {ν' : Measure (QuotientSpace (U := U') U)}
    (hν' : QuotientIntegration.IsCompatible (U'.subgroupOf U) μU μI' ν')
    {μ : Measure G} [μ.IsHaarMeasure] [SFinite μ]
    (hM : IsClosed (M : Set G))
    (hsq : SquaredModulusCompatibility h' hU' h hU)
    (hfull : domain h hU U' (A.twist χ₁ hχ₁) ν = ⊤) :
    domain h' hU' U (A.twist χ₂ hχ₂) ν' ≃ₗ[ℂ]
      (DynamicNormalization.leviTwistedInductionFunctor h' hU').obj (A.twist χ₂ hχ₂) :=
  (LinearEquiv.ofEq _ _ (domain_eq_top_of_forward h hU h' hU' b hbot K hK hPK hP'K hP hP' hr hr' hrec hχ
    hcofinal hA (μM := μM) hμI hμI' hν hν' (μ := μ) hM hsq hfull)).trans
    Submodule.topEquiv

end Langlands.Plancherel.OppositeIntertwiningHermitianAdjunction
