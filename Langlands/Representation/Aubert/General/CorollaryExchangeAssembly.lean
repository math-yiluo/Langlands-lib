import Langlands.Representation.Aubert.GeneralCorollaryTargets
import Langlands.Representation.Aubert.GeneralWeylConjugacyTarget

/-! # Exact-K0 calculation for the rank-one constituent exchange -/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Aubert.General

universe uI uG uV

open SmoothRep

section ExactClasses

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Either orientation of the actual length-two sequence gives the same
exact-K0 sum. No splitting is used. -/
theorem HasTwoConstituents.class_eq
    {A ρplus ρminus : SmoothRep.{0, uG, uV} ℂ G}
    (hseq : HasTwoConstituents A ρplus ρminus)
    (hA : A.HasFiniteLength) (hplus : ρplus.HasFiniteLength)
    (hminus : ρminus.HasFiniteLength) :
    FiniteLengthGrothendieckGroup.ofRepresentation A hA =
      FiniteLengthGrothendieckGroup.ofRepresentation ρplus hplus +
      FiniteLengthGrothendieckGroup.ofRepresentation ρminus hminus := by
  rcases hseq.2.2 with ⟨f, g, hfg⟩ | ⟨f, g, hfg⟩
  · exact FiniteLengthGrothendieckGroup.ofRepresentation_shortExact hplus hA hminus hfg
  · simpa only [add_comm] using
      FiniteLengthGrothendieckGroup.ofRepresentation_shortExact hminus hA hplus hfg

/-- Categorical zero objects have zero class in the actual exact quotient. -/
theorem class_eq_zero_of_isZero
    (A : SmoothRep.{0, uG, uV} ℂ G) (hA : A.HasFiniteLength) (hz : IsZero A) :
    FiniteLengthGrothendieckGroup.ofRepresentation A hA = 0 := by
  have hzero (a : A) : a = 0 :=
    congrArg (fun f : A ⟶ A => SmoothRep.hom f a) (hz.eq_of_src (𝟙 A) 0)
  have hseq : IsShortExact
      (0 : A.representation.IntertwiningMap A.representation)
      (0 : A.representation.IntertwiningMap A.representation) := by
    refine ⟨fun a b _ => (hzero a).trans (hzero b).symm,
      fun a => ⟨0, (hzero a).symm⟩, ?_⟩
    ext a
    simp only [LinearMap.mem_range, LinearMap.mem_ker]
    exact iff_of_true ⟨0, (hzero a).symm⟩ rfl
  have he := FiniteLengthGrothendieckGroup.ofRepresentation_shortExact hA hA hA hseq
  exact add_left_cancel (show
      FiniteLengthGrothendieckGroup.ofRepresentation A hA +
          FiniteLengthGrothendieckGroup.ofRepresentation A hA =
        FiniteLengthGrothendieckGroup.ofRepresentation A hA + 0 by
    simpa only [add_zero] using he.symm)

end ExactClasses

section Operator

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI} [Fintype ι] [DecidableEq ι]
variable (P M U : Finset ι → Subgroup G)
  (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
  (hU : ∀ I, IsClosed (U I : Set G))
  (hfl : ∀ I, ParabolicFiniteLength.{uG, max uG uV} (h I) (hU I))

/-- The support-signed Aubert operator used for the two constituent classes in
Corollary 1.10(b). The underlying alternating operator remains unadjusted. -/
def signedAlternatingOperator (J : Finset ι) :
    FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ G →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ G :=
  ((-1 : ℤ) ^ J.card) • alternatingOperator P M U h hU hfl

omit [Fintype ι] [DecidableEq ι] in
/-- The contribution of a zero actual Jacquet module vanishes. -/
theorem alternatingTerm_eq_zero_of_isZero (I : Finset ι)
    (A : FiniteLengthObject.{0, uG, max uG uV} ℂ G)
    (hz : IsZero ((jacquetFunctor (h I) (hU I)).obj A.val)) :
    alternatingTerm P M U h hU hfl I
      (FiniteLengthGrothendieckGroup.ofObject A) = 0 := by
  change inductionK0 (h I) (hU I) (hfl I).1 (hfl I).2.1
    (jacquetK0 (h I) (hU I) (hfl I).2.2.1 (hfl I).2.2.2
      (FiniteLengthGrothendieckGroup.ofRepresentation A.val A.property)) = 0
  rw [jacquetK0_ofRepresentation,
    class_eq_zero_of_isZero _ _ hz, map_zero]

omit [Fintype ι] [DecidableEq ι] in
/-- An actual Jacquet isomorphism identifies the corresponding induced term. -/
theorem alternatingTerm_eq_induction_of_jacquet_iso (I : Finset ι)
    (A : FiniteLengthObject.{0, uG, max uG uV} ℂ G)
    (σ : FiniteLengthObject.{0, uG, max uG uV} ℂ (M I))
    (e : (jacquetFunctor (h I) (hU I)).obj A.val ≅ σ.val) :
    alternatingTerm P M U h hU hfl I (FiniteLengthGrothendieckGroup.ofObject A) =
      inductionK0 (h I) (hU I) (hfl I).1 (hfl I).2.1
        (FiniteLengthGrothendieckGroup.ofObject σ) := by
  change inductionK0 (h I) (hU I) (hfl I).1 (hfl I).2.1
    (jacquetK0 (h I) (hU I) (hfl I).2.2.1 (hfl I).2.2.2
      (FiniteLengthGrothendieckGroup.ofRepresentation A.val A.property)) = _
  rw [jacquetK0_ofRepresentation]
  exact congrArg _ (FiniteLengthGrothendieckGroup.ofObject_eq_of_iso e)

omit [DecidableEq ι] in
/-- Every term is accounted for: only the specified proper subset and the full
subset remain when all the other actual proper Jacquet modules vanish. -/
theorem alternatingOperator_eq_two_terms (J : Finset ι) (hJ : J ≠ Finset.univ)
    (A : FiniteLengthObject.{0, uG, max uG uV} ℂ G)
    (hz : ∀ K : Finset ι, K ≠ Finset.univ → K ≠ J →
      IsZero ((jacquetFunctor (h K) (hU K)).obj A.val)) :
    alternatingOperator P M U h hU hfl (FiniteLengthGrothendieckGroup.ofObject A) =
      ((-1 : ℤ) ^ J.card) •
        alternatingTerm P M U h hU hfl J (FiniteLengthGrothendieckGroup.ofObject A) +
      ((-1 : ℤ) ^ (Finset.univ : Finset ι).card) •
        alternatingTerm P M U h hU hfl Finset.univ
          (FiniteLengthGrothendieckGroup.ofObject A) := by
  rw [alternatingOperator, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply]
  apply Finset.sum_eq_add_of_mem J Finset.univ (by simp) (by simp) hJ
  intro K _ hK
  rw [alternatingTerm_eq_zero_of_isZero P M U h hU hfl K A (hz K hK.2 hK.1)]
  exact smul_zero _

/-- The maximal-subset condition gives opposite signs in the proper and full
terms, including when the maximal subset itself is empty. -/
theorem IsMaximalStandard.sign_mul (J : Finset ι) (hJ : IsMaximalStandard J) :
    ((-1 : ℤ) ^ J.card) * ((-1 : ℤ) ^ (Finset.univ : Finset ι).card) = -1 := by
  obtain ⟨α, rfl⟩ := hJ
  rw [← Finset.card_erase_add_one (Finset.mem_univ α), pow_succ,
    ← mul_assoc, ← mul_pow]
  simp

/-- The signed calculation from two identified actual terms and an exact class
sum. The full term is supplied explicitly rather than silently identified. -/
theorem signed_exchange_of_two_terms (J : Finset ι) (hJ : IsMaximalStandard J)
    (A : FiniteLengthObject.{0, uG, max uG uV} ℂ G)
    (σ : FiniteLengthObject.{0, uG, max uG uV} ℂ (M J))
    (ρplus ρminus : FiniteLengthObject.{0, uG, max uG uV} ℂ G)
    (hseq : HasTwoConstituents ((normalizedInductionFunctor (h J) (hU J)).obj σ.val)
      ρplus.val ρminus.val)
    (hproper : ∀ K : Finset ι, K ≠ Finset.univ → K ≠ J →
      IsZero ((jacquetFunctor (h K) (hU K)).obj A.val))
    (hterm : alternatingTerm P M U h hU hfl J
      (FiniteLengthGrothendieckGroup.ofObject A) =
      inductionK0 (h J) (hU J) (hfl J).1 (hfl J).2.1
        (FiniteLengthGrothendieckGroup.ofObject σ))
    (htop : alternatingTerm P M U h hU hfl Finset.univ
      (FiniteLengthGrothendieckGroup.ofObject A) =
      FiniteLengthGrothendieckGroup.ofObject A) :
    ((-1 : ℤ) ^ J.card) • alternatingOperator P M U h hU hfl
      (FiniteLengthGrothendieckGroup.ofObject A) =
      FiniteLengthGrothendieckGroup.ofObject ρplus +
        FiniteLengthGrothendieckGroup.ofObject ρminus -
          FiniteLengthGrothendieckGroup.ofObject A := by
  have hneq : J ≠ Finset.univ := by
    obtain ⟨α, rfl⟩ := hJ
    exact Finset.erase_ne_self.mpr (Finset.mem_univ α)
  have hsq : ((-1 : ℤ) ^ J.card) * ((-1 : ℤ) ^ J.card) = 1 := by
    rw [← mul_pow]
    simp
  rw [alternatingOperator_eq_two_terms P M U h hU hfl J hneq A hproper,
    hterm, htop, smul_add, smul_smul, smul_smul, hsq, hJ.sign_mul,
    one_smul, neg_one_smul]
  change inductionK0 (h J) (hU J) (hfl J).1 (hfl J).2.1
    (FiniteLengthGrothendieckGroup.ofRepresentation σ.val σ.property) + _ = _
  rw [inductionK0_ofRepresentation, hseq.class_eq
    ((hfl J).1 σ.val σ.property) ρplus.property ρminus.property]
  simp only [sub_eq_add_neg]
  rfl

/-- The actual Jacquet pattern, induced Weyl class equality and full term
identity imply both signed constituent exchanges. These hypotheses are exposed
as the inputs of the additive assembly, not as a proof of their realization. -/
theorem constituentExchange_of_jacquet_pattern
    (T : Subgroup G) (J : Finset ι) (hJ : IsMaximalStandard J)
    (σ : FiniteLengthObject.{0, uG, max uG uV} ℂ (M J))
    (ρplus ρminus : FiniteLengthObject.{0, uG, max uG uV} ℂ G)
    (n : Langlands.Group.RelativeWeyl.normalizer T)
    (hself : ∀ x : G, x ∈ M J ↔ (n : G) * x * (n : G)⁻¹ ∈ M J)
    (hseq : HasTwoConstituents ((normalizedInductionFunctor (h J) (hU J)).obj σ.val)
      ρplus.val ρminus.val)
    (hpattern : RankOneJacquetPattern P M U h hU T J σ.val ρplus.val ρminus.val n hself)
    (hWeyl : inducedClassWeylConjugacy T P M U h hU hfl)
    (htopPlus : alternatingTerm P M U h hU hfl Finset.univ
      (FiniteLengthGrothendieckGroup.ofObject ρplus) =
      FiniteLengthGrothendieckGroup.ofObject ρplus)
    (htopMinus : alternatingTerm P M U h hU hfl Finset.univ
      (FiniteLengthGrothendieckGroup.ofObject ρminus) =
      FiniteLengthGrothendieckGroup.ofObject ρminus) :
    ConstituentExchange P M U h hU hfl J ρplus ρminus := by
  obtain ⟨eplus⟩ := hpattern.1
  obtain ⟨eminus⟩ := hpattern.2.1
  have htermPlus := alternatingTerm_eq_induction_of_jacquet_iso
    P M U h hU hfl J ρplus σ eplus
  let σn : FiniteLengthObject.{0, uG, max uG uV} ℂ (M J) :=
    ⟨(conjugationFunctor (n : G)⁻¹ (fun x => by simpa using hself x)).obj σ.val,
      pullbackFunctor_preservesFiniteLength
        (conjugationEquiv (n : G)⁻¹ (fun x => by simpa using hself x)) σ.val σ.property⟩
  have hconj : inductionK0 (h J) (hU J) (hfl J).1 (hfl J).2.1
      (FiniteLengthGrothendieckGroup.ofObject σn) =
      inductionK0 (h J) (hU J) (hfl J).1 (hfl J).2.1
        (FiniteLengthGrothendieckGroup.ofObject σ) := by
    change inductionK0 (h J) (hU J) (hfl J).1 (hfl J).2.1
        (FiniteLengthGrothendieckGroup.ofRepresentation σn.val σn.property) =
      inductionK0 (h J) (hU J) (hfl J).1 (hfl J).2.1
        (FiniteLengthGrothendieckGroup.ofRepresentation σ.val σ.property)
    rw [inductionK0_ofRepresentation, inductionK0_ofRepresentation]
    exact hWeyl J J n⁻¹ (fun x => by simpa using hself x) σ
  have htermMinus := (alternatingTerm_eq_induction_of_jacquet_iso
    P M U h hU hfl J ρminus σn eminus).trans hconj
  constructor
  · rw [signed_exchange_of_two_terms P M U h hU hfl J hJ ρplus σ ρplus ρminus
      hseq (fun K hK hKJ => (hpattern.2.2 K hK hKJ).1) htermPlus htopPlus]
    abel
  · rw [signed_exchange_of_two_terms P M U h hU hfl J hJ ρminus σ ρplus ρminus
      hseq (fun K hK hKJ => (hpattern.2.2 K hK hKJ).2) htermMinus htopMinus]
    abel

end Operator

end Langlands.Aubert.General
