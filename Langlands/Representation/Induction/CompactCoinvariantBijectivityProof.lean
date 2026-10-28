import Langlands.Representation.Induction.CompactCoinvariantBijectivityStatement
import Langlands.Representation.Induction.CompactCoinvariantLocalInverseProof
import Langlands.Representation.Induction.CompactLocalSectionSpanningProof
import Langlands.Representation.Induction.CompactLocalSection
import Langlands.Analysis.Local.QuotientMass

noncomputable section

namespace Langlands.Induction

open MeasureTheory MeasureTheory.Measure Topology
open Langlands.HarmonicAnalysis

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (H : Subgroup G) (σ : Representation ℂ H V)
variable [MeasurableSpace (QuotientIntegration.LeftQuotient H)]
variable [BorelSpace (QuotientIntegration.LeftQuotient H)]

private theorem quotientCoinvariantSimple_section_one
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (v : V)
    (hv : v ∈ fixedVectors σ (conjOpenSubgroup H K 1).toSubgroup) :
    quotientCoinvariantSimple H σ (compactDoubleCosetSection H σ K hK 1 v hv) =
      (SimpleFunc.const (QuotientIntegration.LeftQuotient H)
        (Representation.Coinvariants.mk σ v)).restrict
          (QuotientIntegration.compactOpenQuotientOrbit H K) := by
  classical
  ext q
  rw [SimpleFunc.restrict_apply _
    (QuotientIntegration.isOpen_compactOpenQuotientOrbit H K).measurableSet]
  by_cases hq : q ∈ QuotientIntegration.compactOpenQuotientOrbit H K
  · rw [Set.indicator_of_mem hq]
    obtain ⟨k, hk, rfl⟩ := hq
    change Representation.Coinvariants.mk σ
      (eval H σ (compactDoubleCosetSection H σ K hK 1 v hv).val k) =
        Representation.Coinvariants.mk σ v
    congr 1
    simpa using compactDoubleCosetSection_apply H σ K hK 1 v hv 1 ⟨k, hk⟩
  · rw [Set.indicator_of_notMem hq]
    change quotientCoinvariantFunction H σ
      (compactDoubleCosetSection H σ K hK 1 v hv) q = 0
    by_contra hn
    have hs := support_quotientCoinvariantFunction_subset H σ
      (compactDoubleCosetSection H σ K hK 1 v hv) hn
    have hs' := compactDoubleCosetSection_support_subset H σ K hK 1 v hv hs
    apply hq
    obtain ⟨k, hk, hkq⟩ := hs'
    refine ⟨k, hk, ?_⟩
    change quotientMap H k = q
    simpa only [one_mul] using hkq

private theorem compactCoinvariantIntegral_section_one
    (ν : Measure (QuotientIntegration.LeftQuotient H)) [IsFiniteMeasureOnCompacts ν]
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (v : V)
    (hv : v ∈ fixedVectors σ (conjOpenSubgroup H K 1).toSubgroup) :
    compactCoinvariantIntegral H σ ν (compactDoubleCosetSection H σ K hK 1 v hv) =
      (Complex.ofReal ((ν (QuotientIntegration.compactOpenQuotientOrbit H K)).toReal)) •
        Representation.Coinvariants.mk σ v := by
  rw [compactCoinvariantIntegral_apply, quotientCoinvariantSimple_section_one]
  exact AlgebraicIntegral.integral_indicator_const _
    (QuotientIntegration.isOpen_compactOpenQuotientOrbit H K).measurableSet _

omit [MeasurableSpace (QuotientIntegration.LeftQuotient H)]
  [BorelSpace (QuotientIntegration.LeftQuotient H)] in
private theorem exists_section_subgroup
    (hG : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (hσ : IsSmooth σ) (v : V) :
    ∃ (K : OpenSubgroup G) (_hK : IsCompact (K : Set G)),
      v ∈ fixedVectors σ (conjOpenSubgroup H K 1).toSubgroup := by
  obtain ⟨L, hL⟩ := hσ v
  obtain ⟨O, hO, he⟩ := IsInducing.subtypeVal.isOpen_iff.mp L.isOpen
  have h1 : (1 : G) ∈ O := by
    have hh : (1 : H) ∈ (Subtype.val : H → G) ⁻¹' O :=
      (Set.ext_iff.mp he (1 : H)).mpr L.one_mem
    exact hh
  obtain ⟨K, hK, hKO⟩ := hG O hO h1
  refine ⟨K, hK, ?_⟩
  intro h
  have hk : ((h : H) : G) ∈ K := by
    simpa using (mem_conjOpenSubgroup.mp h.property)
  exact hL ⟨h, (Set.ext_iff.mp he (h : H)).mp (hKO hk)⟩

private theorem compactCoinvariantDesc_surjective
    (hG : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (hσ : IsSmooth σ)
    [MeasurableSpace G] [MeasurableSpace H] [MeasurableMul H]
    (μG : Measure G) (μH : Measure H) [IsMulRightInvariant μH]
    (ν : Measure (QuotientIntegration.LeftQuotient H)) [IsFiniteMeasureOnCompacts ν]
    (hν : QuotientIntegration.IsCompatible H μG μH ν) :
    Function.Surjective (compactCoinvariantDesc H σ ν hν.right_invariant) := by
  intro q
  obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective σ q
  obtain ⟨K, hK, hv⟩ := exists_section_subgroup H σ hG hσ v
  have hm := hν.compactOpenQuotientOrbit_mass K hK
  let c : ℂ := Complex.ofReal ((ν (QuotientIntegration.compactOpenQuotientOrbit H K)).toReal)
  have hc : c ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (ENNReal.toReal_pos hm.1.ne' hm.2.ne))
  refine ⟨c⁻¹ • Representation.Coinvariants.mk (compactInduced H σ)
    (compactDoubleCosetSection H σ K hK 1 v hv), ?_⟩
  rw [map_smul, compactCoinvariantDesc_mk, compactCoinvariantIntegral_section_one]
  change c⁻¹ • (c • Representation.Coinvariants.mk σ v) = _
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul]

private theorem compactCoinvariantDesc_bijective_of_local_data
    (hG : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (hσ : IsSmooth σ)
    [MeasurableSpace G] [MeasurableSpace H] [MeasurableMul H]
    (μG : Measure G) (μH : Measure H) [IsMulRightInvariant μH]
    (ν : Measure (QuotientIntegration.LeftQuotient H)) [IsFiniteMeasureOnCompacts ν]
    (hν : QuotientIntegration.IsCompatible H μG μH ν)
    (T : Representation.Coinvariants σ →ₗ[ℂ]
      Representation.Coinvariants (compactInduced H σ))
    (hT : ∀ (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (v : V)
      (hv : v ∈ fixedVectors σ (conjOpenSubgroup H K 1).toSubgroup),
      T (Representation.Coinvariants.mk σ v) =
        (Complex.ofReal ((ν (QuotientIntegration.compactOpenQuotientOrbit H K)).toReal))⁻¹ •
          Representation.Coinvariants.mk (compactInduced H σ)
            (compactDoubleCosetSection H σ K hK 1 v hv))
    (hspan : Submodule.span ℂ {f : CompactFunctions H σ |
      ∃ (g : G) (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (v : V)
        (hv : v ∈ fixedVectors σ (conjOpenSubgroup H K 1).toSubgroup),
        f = compactInduced H σ g (compactDoubleCosetSection H σ K hK 1 v hv)} = ⊤) :
    Function.Bijective (compactCoinvariantDesc H σ ν hν.right_invariant) := by
  have hleft : Function.LeftInverse T
      (compactCoinvariantDesc H σ ν hν.right_invariant) := by
    intro q
    obtain ⟨f, rfl⟩ := Representation.Coinvariants.mk_surjective (compactInduced H σ) q
    have hf : f ∈ Submodule.span ℂ {f : CompactFunctions H σ |
        ∃ (g : G) (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (v : V)
          (hv : v ∈ fixedVectors σ (conjOpenSubgroup H K 1).toSubgroup),
          f = compactInduced H σ g (compactDoubleCosetSection H σ K hK 1 v hv)} := by
      rw [hspan]
      trivial
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨g, K, hK, v, hv, rfl⟩ := hf
      rw [Representation.Coinvariants.mk_self_apply, compactCoinvariantDesc_mk,
        compactCoinvariantIntegral_section_one, map_smul, hT]
      have hm := hν.compactOpenQuotientOrbit_mass K hK
      have hc : Complex.ofReal
          ((ν (QuotientIntegration.compactOpenQuotientOrbit H K)).toReal) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (ne_of_gt (ENNReal.toReal_pos hm.1.ne' hm.2.ne))
      rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
    | zero => simp only [map_zero]
    | add x y hx hy ihx ihy => simp only [map_add, ihx, ihy]
    | smul c x hx ih => simp only [map_smul, ih]
  exact ⟨hleft.injective, compactCoinvariantDesc_surjective H σ hG hσ μG μH ν hν⟩

private theorem compactCoinvariantIntegralBijective_of_prerequisites
    (hlocal : CompactCoinvariantLocalInverseExists.{uG,uV})
    (hspan : CompactLocalSectionSpanning.{uG,uV}) :
    CompactCoinvariantIntegralBijective.{uG,uV} := by
  intro G _ _ _ _ _ _ _ hG H hH _ _ μG μH _ _ _ _ _ _ _ _ ν _ hν V _ _ σ hσ
  obtain ⟨T, hT⟩ := hlocal hG H hH μG μH ν hν V σ hσ
  exact compactCoinvariantDesc_bijective_of_local_data H σ hG hσ μG μH ν hν
    T hT (hspan G hG H hH V σ)

/-- The actual supplied compatible quotient integral is bijective on ambient
coinvariants, with independent group and coefficient universes. -/
theorem compactCoinvariantIntegralBijective :
    CompactCoinvariantIntegralBijective.{uG, uV} :=
  compactCoinvariantIntegralBijective_of_prerequisites
    compactCoinvariantLocalInverseExists compactLocalSectionSpanning

end Langlands.Induction
