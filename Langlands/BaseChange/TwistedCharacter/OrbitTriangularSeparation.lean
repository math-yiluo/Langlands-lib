import Langlands.BaseChange.TwistedCharacter.ProperInductionExpansion
import Langlands.BaseChange.TwistedCharacter.GroupedHeadOrbit
import Langlands.BaseChange.TwistedCharacter.StableClassLines
import Langlands.BaseChange.TwistedCharacter.LeadingHeadTrace
import Langlands.BaseChange.TwistedCharacter.TriangularSpan
import Langlands.BaseChange.TwistedCharacter.StandardTraceSpan
import Langlands.BaseChange.TwistedPseudoCoefficientOrbitSeparation
import Langlands.Representation.Classification.MultisegmentHeadClassificationProof
import Langlands.Representation.Classification.RegularLanglandsHeadExistenceProof
import Langlands.Representation.Classification.TwoFactorProductConstituentCommutativityProof

/-! # Triangular separation of the orbit of a σ-discrete series -/

noncomputable section

namespace Langlands.BaseChange

open CategoryTheory Classification GeneralLinear HarmonicAnalysis MeasureTheory
open PadicField.TopologicalData

universe u v z

section Rank

variable {p : ℕ} [Fact p.Prime] {E : PadicField.{v} p} {T : E.TopologicalData}

/-- The numerical measure of the rank order on multisegments. -/
def headRankMeasure (a : T.Multisegment.{max v z, v}) : ℕ :=
  (Multisegment.candidateSegments a.cuspidalContent).card * Multiset.card a.cuspidalContent -
    Multisegment.rankMeasure a.cuspidalContent a

theorem headRankMeasure_lt {a b : T.Multisegment.{max v z, v}} (h : b.RankLE a) (hne : b ≠ a) :
    headRankMeasure b < headRankMeasure a := by
  have hlt := Multisegment.rankMeasure_lt h hne
  have hb := Multisegment.rankMeasure_le b
  rw [h.1] at hb
  unfold headRankMeasure
  rw [h.1]
  omega

end Rank

section Padic

variable {F : Type u} [Field F] [TopologicalSpace F] {p : ℕ} [Fact p.Prime]
  {E : PadicField.{v} p} [Algebra F E.Carrier] (T : E.TopologicalData)
  (hModule : letI := T.topology; IsModuleTopology F E.Carrier)
  (σ : E.Carrier ≃ₐ[F] E.Carrier)

set_option maxHeartbeats 6400000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- The twisted-character span of the orbit of a σ-discrete series is disjoint from the sum
of the spans of the other essentially tempered classes and of proper σ-inductions. -/
theorem disjoint_twistedOrbitSpan_otherTempered_sup_properInduced {n : ℕ} (hn : 0 < n)
    {d : ℕ} (hd : 0 < d) (hσ : σ ^ d = 1)
    {W : Type z} [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GeneralLinear n E.Carrier) W)
    (hτ : letI := T.topology; letI := T.valuativeRel; letI := T.localField;
      IsSigmaDiscreteSeries σ n τ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := hModule
    ∀ [T2Space (GeneralLinear n E.Carrier)]
      [LocallyCompactSpace (GeneralLinear n E.Carrier)]
      [TotallyDisconnectedSpace (GeneralLinear n E.Carrier)]
      [MeasurableSpace (GeneralLinear n E.Carrier)] [BorelSpace (GeneralLinear n E.Carrier)]
      (μ : Measure (GeneralLinear n E.Carrier)) [μ.IsHaarMeasure],
      Disjoint (twistedOrbitSpan μ (entrywiseAut σ n) τ)
        (twistedOtherEssentiallyTemperedSpan μ (entrywiseAut σ n) τ ⊔
          sigmaProperInducedSpan.{u,v,z} σ μ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := hModule
  let := T.generalLinearTopologicalGroup n
  intro _ _ _ _ _ μ _
  let θ := entrywiseAut σ n
  have hθ := exists_compact_openSubgroup_symm_mem θ (continuous_entrywiseAut σ n) d hd (by
    intro g
    change (⇑(entrywiseAut σ n))^[d] g = g
    rw [entrywiseAut_iterate_eq_pow, hσ, entrywiseAut_one_apply])
  let x (c : StableIrreducibleClass.{v, max v z} θ) : Distribution (GeneralLinear n E.Carrier) :=
    c.trace θ μ
  have hli : LinearIndependent ℂ x := linearIndependent_stableIrreducibleClass_trace θ μ hθ
  have hdata (c : StableIrreducibleClass.{v, max v z} θ) :
      ∃ (t : T.TemperedLanglandsDatum.{max v z} n)
        (A : ∀ i, SigmaIntertwiner σ (t.shape.size i) (t.blocks i).representation)
        (a : T.Multisegment.{max v z, v}),
        t.IsLanglandsHead (c.rep θ).obj ∧ a.IsLanglandsHead (c.rep θ).obj ∧
          t.standardModule.HasFiniteLength ∧
          ∀ (b : T.Multisegment.{max v z, v})
            (D : SmoothRep.{0,v,max v z} ℂ (GeneralLinear n E.Carrier)),
            b.IsLanglandsHead D →
            SmoothRep.IsSubquotient D (t.standardModule.subrepresentation
              (headKernel t.standardModule.representation)) →
            b.RankLE a ∧ b ≠ a := by
    obtain ⟨t, ht, hst⟩ := exists_sigmaStable_temperedLanglandsHead.{u,v,z} F p E T hModule σ n hn
      (c.rep θ).obj (c.rep θ).property.1 (c.rep θ).property.2 ⟨c.intertwiner θ⟩
    obtain ⟨a, ha, hfin, hord⟩ := temperedLanglandsHeadOrder.{v,z} p E T n hn t (c.rep θ).obj ht
    exact ⟨t, fun i => (hst i).some, a, ht, ha, hfin, hord⟩
  choose tc Ac ac hhead hac hfin hord using hdata
  let rank (c : StableIrreducibleClass.{v, max v z} θ) : ℕ := headRankMeasure (ac c)
  let y (c : StableIrreducibleClass.{v, max v z} θ) : Distribution (GeneralLinear n E.Carrier) :=
    twistedDistribution μ (tc c).standardModule.representation
      (temperedStandard_isAdmissible T (tc c))
      (temperedStandardSigmaIntertwiner T hModule σ (tc c) (Ac c)).toLinearMap
  have htri (c : StableIrreducibleClass.{v, max v z} θ) : ∃ a : ℂ, a ≠ 0 ∧
      y c - a • x c ∈ Submodule.span ℂ (x '' {j | rank j < rank c}) := by
    refine twistedDistribution_sub_smul_head_mem μ θ _ (tc c).standardModule
      (temperedStandard_isAdmissible T (tc c)) (hfin c)
      (temperedStandardSigmaIntertwiner T hModule σ (tc c) (Ac c)) (c.rep θ).obj
      (c.rep θ).property.2 (hhead c) (c.intertwiner θ) ?_ ?_
    · exact hli.notMem_span_image (fun h => lt_irrefl (rank c) h)
    · intro D hD hDirr hsub AD
      obtain ⟨b, -, hb⟩ := multisegmentHeadExhaustion.{v,z} E T n D hDirr
      have hlt := hord c b D hb hsub
      let cD : StableIrreducibleClass.{v, max v z} θ :=
        StableIrreducibleClass.mk θ D.representation hD hDirr AD
      have hcD := StableIrreducibleClass.nonempty_rep_equiv_mk θ D.representation hD hDirr AD
      have hacD : ac cD = b := (multisegmentHeadClassification E T n (ac cD) b (cD.rep θ).obj D
        (hac cD) hb).mpr ⟨SmoothRep.mkIso hcD.some⟩
      have hrank : rank cD < rank c := by
        change headRankMeasure (ac cD) < headRankMeasure (ac c)
        rw [hacD]
        exact headRankMeasure_lt hlt.1 hlt.2
      obtain ⟨α, hα⟩ := twistedDistribution_eq_smul_stableIrreducibleClass_trace θ μ
        D.representation hD AD cD hcD
      rw [hα]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨cD, hrank, rfl⟩)
  let P : Set (StableIrreducibleClass.{v, max v z} θ) :=
    {c | IsUnramifiedTwistOf θ τ (c.rep θ).obj.representation}
  let Q : Set (StableIrreducibleClass.{v, max v z} θ) := Pᶜ
  have hdisj := triangularSpanSeparation (k := ℂ) x y rank P Q hli disjoint_compl_right
    (fun c _ => htri c)
  have horbit {X : Type (max v z)} [AddCommGroup X] [Module ℂ X]
      {ρ : Representation ℂ (GeneralLinear n E.Carrier) X}
      (c : StableIrreducibleClass.{v, max v z} θ)
      (hc : Nonempty ((c.rep θ).obj.representation.Equiv ρ)) :
      c ∈ P ↔ IsUnramifiedTwistOf θ τ ρ := by
    constructor
    · rintro ⟨ψ, hψ, hψθ, ⟨e⟩⟩
      exact ⟨ψ, hψ, hψθ, ⟨hc.some.symm.trans e⟩⟩
    · rintro ⟨ψ, hψ, hψθ, ⟨e⟩⟩
      exact ⟨ψ, hψ, hψθ, ⟨hc.some.trans e⟩⟩
  have hlift {X : Type z} [AddCommGroup X] [Module ℂ X]
      (ρ : Representation ℂ (GeneralLinear n E.Carrier) X) (hρ : IsAdmissible ρ)
      (hirr : ρ.IsIrreducible) (A : ρ.Equiv (ρ.comp θ.toMonoidHom)) :
      ∃ c : StableIrreducibleClass.{v, max v z} θ, ∃ α : ℂ,
        Nonempty ((c.rep θ).obj.representation.Equiv (universeLiftRepresentation.{v} ρ)) ∧
        twistedDistribution μ ρ hρ A.toLinearMap = α • x c := by
    let ρu := universeLiftRepresentation.{v} ρ
    let eu := universeLiftEquiv.{v} ρ
    let Au := SigmaIntertwiner.transport (σ := σ) A eu
    have hρu : IsAdmissible ρu := (isAdmissible_universeLift_iff ρ).mpr hρ
    have hirru := (isIrreducible_universeLift_iff ρ).mpr hirr
    let c := StableIrreducibleClass.mk θ ρu hρu hirru Au
    have hc := StableIrreducibleClass.nonempty_rep_equiv_mk θ ρu hρu hirru Au
    obtain ⟨α, hα⟩ := twistedDistribution_eq_smul_stableIrreducibleClass_trace θ μ ρu hρu Au c hc
    refine ⟨c, α, hc, ?_⟩
    rw [← twistedDistribution_eq_of_equivalent μ hρ hρu eu A.toLinearMap]
    exact hα
  have hL : twistedOrbitSpan μ θ τ ≤ Submodule.span ℂ (x '' P) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨X, iAdd, iMod, ρ, hρ, A, hirr, horb, rfl⟩
    let := iAdd
    let := iMod
    obtain ⟨c, α, hc, hα⟩ := hlift ρ hρ hirr A
    rw [hα]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, ?_, rfl⟩)
    obtain ⟨ψ, hψ, hψθ, ⟨e⟩⟩ := horb
    exact (horbit c hc).mpr ⟨ψ, hψ, hψθ, ⟨(universeLiftEquiv.{v} ρ).symm.trans e⟩⟩
  have hO : twistedOtherEssentiallyTemperedSpan μ θ τ ≤ Submodule.span ℂ (y '' Q) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨X, iAdd, iMod, ρ, hρ, A, hirr, ⟨hnot, ψ, hψ, hψθ, htempψ⟩, rfl⟩
    let := iAdd
    let := iMod
    obtain ⟨c, α, hc, hα⟩ := hlift ρ hρ hirr A
    rw [hα]
    refine Submodule.smul_mem _ _ ?_
    have hcQ : c ∈ Q := fun hcP => hnot (by
      obtain ⟨ψ', hψ', hψ'θ, ⟨e'⟩⟩ := (horbit c hc).mp hcP
      exact ⟨ψ', hψ', hψ'θ, ⟨(universeLiftEquiv.{v} ρ).trans e'⟩⟩)
    have hct : T.IsTempered (twist ψ (c.rep θ).obj.representation) := by
      have e' : (twist ψ (c.rep θ).obj.representation).Equiv (twist ψ ρ) :=
        twistEquiv ψ (hc.some.trans (universeLiftEquiv.{v} ρ).symm)
      exact (T.isTempered_iff_of_equiv e').mpr ((isTemperedRep_iff_isTempered T _).mp htempψ)
    have h1 := shape_length_eq_one_of_twist_tempered.{v,z} T hn (tc c) (c.rep θ).obj
      (hhead c).isLanglandsQuotient ψ hψ hct
    have hMirr := (singleBlockStandard_irreducible_essentiallyTempered T hModule σ (tc c) h1).1
    obtain ⟨eM⟩ := nonempty_equiv_of_isIrreducibleHead_of_isIrreducible hMirr (hhead c)
    obtain ⟨β, hβ⟩ := exists_twistedDistribution_eq_smul_of_equiv μ θ
      (temperedStandard_isAdmissible T (tc c)) hMirr (c.rep θ).property.2 eM
      (temperedStandardSigmaIntertwiner T hModule σ (tc c) (Ac c)) (c.intertwiner θ)
    change x c ∈ _
    rw [show x c = β • y c from hβ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, hcQ, rfl⟩)
  have hI : sigmaProperInducedSpan.{u,v,z} σ μ ≤ Submodule.span ℂ (y '' Q) := by
    refine (sigmaProperInducedSpan_le_span_flatRealFamilySet.{u,v,z} T hModule σ hd hσ μ).trans ?_
    apply Submodule.span_le.mpr
    rintro _ ⟨L, hL, δ, hirrδ, htempδ, Aδ, xs, rfl⟩
    obtain ⟨t, A', qq, cc, -, -, hunit, hD⟩ := exists_standardTrace_eq_smul_blockFamilyTrace T
      hModule σ hn L δ hirrδ htempδ Aδ hd hσ xs μ
    rw [hD]
    refine Submodule.smul_mem _ _ ?_
    obtain ⟨π, hπ⟩ := glRegularLanglandsHeadExistence.{v,z} p E T n hn t
    obtain ⟨Aπ⟩ := nonempty_twistingEquiv_of_isIrreducibleHead θ
      (temperedStandardSigmaIntertwiner T hModule σ t A') hπ
    have hπirr : π.representation.IsIrreducible := hπ.1
    have hπadm : IsAdmissible π.representation :=
      TwoFactorCommutativity.isAdmissible_of_isIrreducible E T π.representation π.isSmooth hπirr
    let c := StableIrreducibleClass.mk θ π.representation hπadm hπirr Aπ
    have hc := StableIrreducibleClass.nonempty_rep_equiv_mk θ π.representation hπadm hπirr Aπ
    have hcQ : c ∈ Q := fun hcP => not_isUnramifiedTwistOf_groupedHead T hModule σ hn L hL δ
      hirrδ htempδ Aδ t qq hunit π hπ τ hτ ((horbit c hc).mp hcP)
    obtain ⟨β, -, hβ⟩ := standardTrace_eq_smul_of_head T hModule σ hn (tc c) t (c.rep θ).obj π
      (hhead c) hπ ⟨SmoothRep.mkIso hc.some⟩ (Ac c) A' hd hσ μ
    rw [hβ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, hcQ, rfl⟩)
  exact hdisj.mono hL (sup_le hO hI)

end Padic

end Langlands.BaseChange
