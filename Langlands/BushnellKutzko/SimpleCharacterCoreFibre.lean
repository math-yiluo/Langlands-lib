import Langlands.BushnellKutzko.SimpleCharacterCore
import Langlands.BushnellKutzko.SimpleCharacterCoherenceReduction
import Langlands.BushnellKutzko.SimpleCharacterCentralizerDeterminant

/-! # The adjacent restriction fibre of a core approximation -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV uG

section Transport

variable {G : Type uG} [Group G] {H K : Subgroup G}

private def transportCharacter (h : H = K) (χ : H →* ℂˣ) : K →* ℂˣ :=
  Eq.ndrec (motive := fun L : Subgroup G => L →* ℂˣ) χ h

private theorem transportCharacter_apply (h : H = K) (χ : H →* ℂˣ) (g : K) :
    transportCharacter h χ g = χ ⟨g, h.symm ▸ g.property⟩ := by
  cases h
  rfl

private theorem transportCharacter_mul (h : H = K) (χ η : H →* ℂˣ) :
    transportCharacter h (χ * η) = transportCharacter h χ * transportCharacter h η := by
  cases h
  rfl

private theorem mem_transportCharacterSet (h : H = K) (C : Set (H →* ℂˣ)) (χ : K →* ℂˣ) :
    χ ∈ transportCharacterSet h C ↔ transportCharacter h.symm χ ∈ C := by
  cases h
  rfl

private theorem characterAgreesOn_mul_of_transport (h : H = K) {θ : H →* ℂˣ} {θ₀ : K →* ℂˣ}
    (η : H →* ℂˣ) {t : G → ℂ} (hag : characterAgreesOn H θ θ₀ t) :
    characterAgreesOn H (θ * η) (θ₀ * transportCharacter h η) t := by
  cases h
  intro g
  obtain ⟨h₁, h₂, he⟩ := hag g
  refine ⟨h₁, h₂, ?_⟩
  simp only [MonoidHom.mul_apply, Units.val_mul]
  change (θ g : ℂ) * η g = ((θ₀ g : ℂ) * η g) * t g
  rw [show (θ g : ℂ) = (θ₀ g : ℂ) * t g from he, mul_right_comm _ (t g)]

private theorem eq_of_characterAgreesOn {θ χ : H →* ℂˣ} {θ₀ : K →* ℂˣ} {t : G → ℂ}
    (hθ : characterAgreesOn H θ θ₀ t) (hχ : characterAgreesOn H χ θ₀ t) : θ = χ := by
  ext g
  obtain ⟨_, _, ha⟩ := hθ g
  obtain ⟨_, _, hb⟩ := hχ g
  exact ha.trans hb.symm

end Transport

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ
local notation "Hc(" S "," q "," m ")" => simpleHGroup (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q) (m + 1)
local notation "Cc(" ψ "," S "," q "," m ")" => simpleCharacters ψ (Stratum.chain S) (Stratum.n S)
  (Stratum.b S) (Stratum.DefiningSequenceChoice.tail q) m

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
set_option maxHeartbeats 800000 in
private theorem factorsThroughCentralizerDet_mul {β : A} {H : Subgroup G} {θ η : H →* ℂˣ}
    (hθ : factorsThroughCentralizerDet β θ) (hη : factorsThroughCentralizerDet β η) :
    factorsThroughCentralizerDet β (θ * η) := by
  obtain ⟨hE, χ, hχ⟩ := hθ
  obtain ⟨hE', χ', hχ'⟩ := hη
  cases Subsingleton.elim hE' hE
  refine ⟨hE, χ * χ', fun x => ?_⟩
  simp only [MonoidHom.mul_apply]
  rw [hχ x, hχ' x]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem mul_mem_of_terminal (ψF : AddChar F ℂ) (L : LatticeChain 𝒪[F] F V)
    (n : ℤ) (β : A) {tail : List A} (htail : tail = []) (m : ℕ)
    {θ η : simpleHGroup L n β tail (m + 1) →* ℂˣ}
    (hθ : θ ∈ simpleCharacters ψF L n β tail m) (hη : factorsThroughCentralizerDet β η)
    (htriv : ∀ g : simpleHGroup L n β tail (m + 1),
      (g : G) ∈ L.unitFiltration (simpleHCutoff n).toNat → η g = 1) :
    θ * η ∈ simpleCharacters ψF L n β tail m := by
  subst tail
  refine ⟨fun g hg => ?_, factorsThroughCentralizerDet_mul hθ.2 hη⟩
  simp only [MonoidHom.mul_apply, htriv g hg, mul_one]
  exact hθ.1 g hg

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem tail_eq_nil_of_scalar {S : Stratum 𝒪[F] F V} (q : S.DefiningSequenceChoice)
    (hs : elementAlgebra S.b = ⊥) : q.tail = [] := by
  apply List.length_eq_zero_iff.mp
  simp only [Stratum.DefiningSequenceChoice.tail, List.length_ofFn]
  by_contra h
  let j : Fin q.steps := ⟨0, Nat.pos_of_ne_zero h⟩
  have hcrit := (q.isDefiningSequence.2.2.2.2.2.1 j).1
  have hj : j.castSucc = 0 := Fin.ext rfl
  rw [hj, q.firstElement] at hcrit
  simp [criticalExponent, hs] at hcrit

/-- Below the half cutoff, a character trivial at the next depth and factoring through
the determinant on the centralizer preserves the simple character set by multiplication. -/
theorem simpleCharacter_mul_mem_of_belowCutoff
    (hrestriction : SimpleCharacterRestrictionStatement.{uF, uV})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    {S : Stratum 𝒪[F] F V} (q : S.DefiningSequenceChoice) (hS : S.IsSimple) (hr : 0 ≤ S.r)
    (m : ℕ) (hm : (m : ℤ) < S.n) (hcut : (m : ℤ) < finiteCriticalDepth S.chain S.n S.b / 2)
    {θ η : Hc(S, q, m) →* ℂˣ} (hθ : θ ∈ Cc(ψF, S, q, m))
    (hη : factorsThroughCentralizerDet S.b η)
    (htriv : ∀ g : Hc(S, q, m), (g : G) ∈ Hc(S, q, (m + 1)) → η g = 1) :
    θ * η ∈ Cc(ψF, S, q, m) := by
  let S₀ := S.atDepthZero (hr.trans_lt S.r_lt_n)
  let q₀ := q.atDepthZero hr
  by_cases hs : elementAlgebra S.b = ⊥
  · have hcut' : (m : ℤ) < S.n / 2 := by
      simpa [finiteCriticalDepth, simpleCriticalDepth, criticalExponent, hs] using hcut
    apply mul_mem_of_terminal ψF S.chain S.n S.b (tail_eq_nil_of_scalar q hs) m hθ hη
    intro g hg
    let d := (S.n / 2).toNat
    have hd : S.n / 2 ≤ (d : ℤ) := by omega
    have hunit : (simpleHCutoff S.n).toNat = d + 1 := by unfold simpleHCutoff; omega
    apply htriv
    apply simpleHGroup_antitone S.chain S.n S.b q.tail (show m + 1 + 1 ≤ d + 1 by omega)
    rwa [simpleHGroup_eq_unitFiltration_of_half_le q d hd, ← hunit]
  · let d := (finiteCriticalDepth S.chain S.n S.b / 2).toNat
    have hmd : m + 1 ≤ d := by omega
    have hle : m ≤ d := by omega
    let res := simpleCharacterRestriction S q hle
    have hres : res η = 1 := by
      apply MonoidHom.ext
      intro g
      exact htriv (Subgroup.inclusion (simpleHGroup_antitone S.chain S.n S.b q.tail
        (show m + 1 ≤ d + 1 by omega)) g)
        (simpleHGroup_antitone S.chain S.n S.b q.tail (show m + 1 + 1 ≤ d + 1 by omega) g.property)
    have hfibre := ((hrestriction F V ψF hψ S₀ rfl (Stratum.isSimple_atDepthZero hS hr) q₀).2.1
      hs m hle hm).2 θ hθ
    change {χ | χ ∈ Cc(ψF, S, q, m) ∧ res χ = res θ} =
      (fun χ => θ * χ) '' {χ | res χ = 1 ∧ factorsThroughCentralizerDet S.b χ} at hfibre
    have hmem : θ * η ∈ (fun χ => θ * χ) '' {χ | res χ = 1 ∧ factorsThroughCentralizerDet S.b χ} :=
      ⟨η, ⟨hres, hη⟩, rfl⟩
    rw [← hfibre] at hmem
    exact hmem.1

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem factorsThroughCentralizerDet_transport {β : A} {H K : Subgroup G}
    (h : H = K) (η : H →* ℂˣ) (hη : factorsThroughCentralizerDet β η) :
    factorsThroughCentralizerDet β (transportCharacter h η) := by
  cases h
  exact hη

/-- A determinant-factorable twist trivial on the adjacent domain preserves membership
in the simple character set of the original stratum, using the core correspondence. -/
theorem SimpleCharacterCore.mul_mem_of_trivial_on_succ
    (hrestriction : SimpleCharacterRestrictionStatement.{uF, uV})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    {S : Stratum 𝒪[F] F V} (q : S.DefiningSequenceChoice) (hrS : 0 ≤ S.r) (m : ℕ)
    (hm : (m : ℤ) < S.n / 2) (core : SimpleCharacterCore ψF S q m)
    (hsucc : Hc(S, q, (m + 1)) = Hc(core.stratum, core.sequence, (m + 1)))
    {θ η : Hc(S, q, m) →* ℂˣ} (hθ : θ ∈ Cc(ψF, S, q, m))
    (hη : factorsThroughCentralizerDet core.stratum.b η)
    (htriv : ∀ g : Hc(S, q, m), (g : G) ∈ Hc(S, q, (m + 1)) → η g = 1) :
    θ * η ∈ Cc(ψF, S, q, m) := by
  obtain ⟨θ₀, hθ₀, hag⟩ := core.twist.1 θ hθ
  let η₀ := transportCharacter core.domain_eq η
  have hη₀ : factorsThroughCentralizerDet core.stratum.b η₀ :=
    factorsThroughCentralizerDet_transport core.domain_eq η hη
  have hk (g : Hc(core.stratum, core.sequence, m))
      (hg : (g : G) ∈ Hc(core.stratum, core.sequence, (m + 1))) : η₀ g = 1 := by
    rw [show η₀ g = η ⟨g, core.domain_eq.symm ▸ g.property⟩ from
      transportCharacter_apply core.domain_eq η g]
    exact htriv ⟨g, core.domain_eq.symm ▸ g.property⟩ (hsucc.symm ▸ hg)
  have hm' : (m : ℤ) < core.stratum.n := by rw [core.level_eq]; omega
  have hθ₀η₀ := simpleCharacter_mul_mem_of_belowCutoff hrestriction ψF hψ core.sequence
    core.isSimple (hrS.trans core.depth_le) m hm' core.below_cutoff hθ₀ hη₀ hk
  obtain ⟨χ, hχ, hag'⟩ := core.twist.2 (θ₀ * η₀) hθ₀η₀
  exact eq_of_characterAgreesOn hag' (characterAgreesOn_mul_of_transport core.domain_eq η hag) ▸ hχ

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem higher_domain_of_carrier (L : LatticeChain 𝒪[F] F V) (n : ℤ)
    (b : A) (tail : List A) {m k : ℕ} (hmk : m ≤ k)
    (hcarrier : ∀ j, (simpleHGroup L n b tail j : Set G) = simpleHCarrier L n b tail j) :
    simpleHGroup L n b tail m ⊓ L.unitFiltration k = simpleHGroup L n b tail k := by
  ext g
  change (g ∈ (simpleHGroup L n b tail m : Set G) ∧ g ∈ L.unitFiltration k) ↔
    g ∈ (simpleHGroup L n b tail k : Set G)
  rw [hcarrier, hcarrier]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨L.unitFiltration_antitone hmk h.1, h.2⟩, h.1⟩⟩

/-- The equality of character domains also holds at deeper filtration indices. -/
theorem SimpleCharacterCore.domain_eq_of_le (hgroups : SimpleStratumGroupPropertiesStatement.{uF, uV})
    {ψF : AddChar F ℂ} {S : Stratum 𝒪[F] F V} {q : S.DefiningSequenceChoice} {m : ℕ}
    (hS : S.IsSimple) (hr : 0 ≤ S.r) (core : SimpleCharacterCore ψF S q m) {k : ℕ} (hmk : m ≤ k) :
    Hc(S, q, k) = Hc(core.stratum, core.sequence, k) := by
  have hc (T : Stratum 𝒪[F] F V) (q' : T.DefiningSequenceChoice)
      (hT : T.IsSimple) (hdepth : 0 ≤ T.r) :
      ∀ j, (simpleHGroup T.chain T.n T.b q'.tail j : Set G) = simpleHCarrier T.chain T.n T.b q'.tail j :=
    fun j => ((hgroups F V (T.atDepthZero (hdepth.trans_lt T.r_lt_n)) rfl
      (Stratum.isSimple_atDepthZero hT hdepth) (q'.atDepthZero hdepth)).1 j).1
  have h₁ := higher_domain_of_carrier S.chain S.n S.b q.tail (Nat.succ_le_succ hmk)
    (hc S q hS hr)
  have h₂ := higher_domain_of_carrier core.stratum.chain core.stratum.n core.stratum.b core.sequence.tail
    (Nat.succ_le_succ hmk) (hc core.stratum core.sequence core.isSimple (hr.trans core.depth_le))
  rw [← h₁, ← h₂, core.domain_eq, core.chain_eq]

private theorem factorsThroughCentralizerDet_of_domain_eq
    (hdet : SimpleCharacterCentralizerDeterminantStatement.{uF, uV})
    {S : Stratum 𝒪[F] F V} (q : S.DefiningSequenceChoice) (hS : S.IsSimple)
    (m : ℕ) {H : Subgroup G} (h : Hc(S, q, m) = H) (η : H →* ℂˣ)
    (hη : (centralizerUnitGroup S.b : Set G) ⊆ characterSelfIntertwining η) :
    factorsThroughCentralizerDet S.b η := by
  cases h
  exact hdet F V S q hS m η hη

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem characterSelfIntertwining_transport {H K : Subgroup G} (h : H = K) (η : H →* ℂˣ) :
    characterSelfIntertwining (transportCharacter h η) = characterSelfIntertwining η := by
  cases h
  rfl

/-- The core comparison used in (3.5.8). The self-intertwining of one common restriction
contains both core centralizers and intertwines the ratios from both original sets. -/
def SimpleCharacterCoreComparisonStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (S T : Stratum 𝒪[F] F V) (q : S.DefiningSequenceChoice) (q' : T.DefiningSequenceChoice),
      S.r = 0 → T.r = 0 → S.IsSimple → T.IsSimple → T.chain.order = S.chain.order → T.n = S.n →
      ∀ (m : ℕ), (m : ℤ) < S.n / 2 → ∀ h : Hc(S, q, m) = Hc(T, q', m),
        let C := transportCharacterSet h (Cc(ψF, S, q, m))
        let D := Cc(ψF, T, q', m)
        ∀ θ ∈ C ∩ D, ∃ (core : SimpleCharacterCore ψF S q m)
            (core' : SimpleCharacterCore ψF T q' m) (k : ℕ) (hmk : m ≤ k),
          let I := characterSelfIntertwining (simpleCharacterRestriction T q' hmk θ)
          (centralizerUnitGroup core.stratum.b : Set (Module.End F V)ˣ) ⊆ I ∧
          (centralizerUnitGroup core'.stratum.b : Set (Module.End F V)ˣ) ⊆ I ∧
          ∀ χ ∈ C ∪ D, I ⊆ characterSelfIntertwining (χ / θ)

/-- Once a common core intertwining set is identified, determinant factorization
and the core twist correspondence establish the kernel test for descent. -/
theorem simpleCharacterCoherenceFibre_of_coreComparison
    (hgroups : SimpleStratumGroupPropertiesStatement.{uF, uV})
    (hrestriction : SimpleCharacterRestrictionStatement.{uF, uV})
    (hdet : SimpleCharacterCentralizerDeterminantStatement.{uF, uV})
    (hcomparison : SimpleCharacterCoreComparisonStatement.{uF, uV}) :
    SimpleCharacterCoherenceFibreStatement.{uF, uV} := by
  intro F _ _ _ _ V _ _ ψF hψ S T q q' hr hr' hS hT horder hn m hm h hnext C D θ hθ
  have hrS : 0 ≤ S.r := by omega
  have hrT : 0 ≤ T.r := by omega
  have hmT : (m : ℤ) < T.n / 2 := hn.symm ▸ hm
  obtain ⟨core, core', k, hmk, hB, hB', hratio⟩ :=
    hcomparison F V ψF hψ S T q q' hr hr' hS hT horder hn m hm h θ hθ
  refine ⟨characterSelfIntertwining (simpleCharacterRestriction T q' hmk θ), hratio, ?_⟩
  intro η hη hintertwining
  have ht (g : Hc(T, q', m)) (hg : (g : (Module.End F V)ˣ) ∈ Hc(T, q', (m + 1))) : η g = 1 :=
    DFunLike.congr_fun hη ⟨g, hg⟩
  have hs (g : Hc(S, q, m)) (hg : (g : (Module.End F V)ˣ) ∈ Hc(S, q, (m + 1))) :
      transportCharacter h.symm η g = 1 :=
    (transportCharacter_apply h.symm η g).trans (ht ⟨g, h ▸ g.property⟩ (hnext ▸ hg))
  have hdetS : factorsThroughCentralizerDet core.stratum.b (transportCharacter h.symm η) := by
    apply factorsThroughCentralizerDet_of_domain_eq hdet core.sequence core.isSimple m core.domain_eq.symm
    rw [characterSelfIntertwining_transport]
    exact hB.trans hintertwining
  have hdetT : factorsThroughCentralizerDet core'.stratum.b η :=
    factorsThroughCentralizerDet_of_domain_eq hdet core'.sequence core'.isSimple m
      core'.domain_eq.symm η (hB'.trans hintertwining)
  refine ⟨?_, core'.mul_mem_of_trivial_on_succ hrestriction ψF hψ q' hrT m hmT
    (core'.domain_eq_of_le hgroups hT hrT (Nat.le_succ m)) hθ.2 hdetT ht⟩
  show θ * η ∈ transportCharacterSet h (Cc(ψF, S, q, m))
  have hθS : transportCharacter h.symm θ ∈ Cc(ψF, S, q, m) :=
    (mem_transportCharacterSet h _ θ).1 hθ.1
  apply (mem_transportCharacterSet h _ _).2
  rw [transportCharacter_mul]
  exact core.mul_mem_of_trivial_on_succ hrestriction ψF hψ q hrS m hm
    (core.domain_eq_of_le hgroups hS hrS (Nat.le_succ m)) hθS hdetS hs

/-- The core intertwining comparison and the structural and determinant results
give the published coherence proposition. -/
def SimpleCharacterCoherenceCoreReductionStatement : Prop :=
  SimpleStratumGroupPropertiesStatement.{uF, uV} →
  SimpleCharacterRestrictionStatement.{uF, uV} →
  SimpleCharacterCentralizerDeterminantStatement.{uF, uV} →
  SimpleCharacterCoreComparisonStatement.{uF, uV} →
  SimpleCharacterCoherenceStatement.{uF, uV}

theorem simpleCharacterCoherenceCoreReduction : SimpleCharacterCoherenceCoreReductionStatement.{uF, uV} :=
  fun hgroups hrestriction hdet hcomparison =>
    simpleCharacterCoherenceReduction hgroups hrestriction
      (simpleCharacterCoherenceFibre_of_coreComparison hgroups hrestriction hdet hcomparison)

end Langlands.BushnellKutzko
