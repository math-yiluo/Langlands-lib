import Langlands.BushnellKutzko.SimpleCharacterRestrictionStatement
import Langlands.BushnellKutzko.SimpleCharacterSequence
import Langlands.BushnellKutzko.SimpleStratumLatticePropertiesStatement
import Langlands.BushnellKutzko.NormalizerProof
import Langlands.BushnellKutzko.AdditiveDualityProof

/-! # Core approximations of simple character sets -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV uG

section CharacterSets

variable {G : Type uG} [Group G] {H K J : Subgroup G}

/-- The specified twist relates the two character sets surjectively in both directions. -/
def CharacterSetTwistCorrespondence (C : Set (H →* ℂˣ)) (D : Set (K →* ℂˣ))
    (twist : G → ℂ) : Prop :=
  (∀ χ ∈ C, ∃ η ∈ D, characterAgreesOn H χ η twist) ∧
  (∀ η ∈ D, ∃ χ ∈ C, characterAgreesOn H χ η twist)

private theorem characterSetTwistCorrespondence_one (C : Set (H →* ℂˣ)) :
    CharacterSetTwistCorrespondence C C (fun _ => 1) := by
  have h (χ : H →* ℂˣ) : characterAgreesOn H χ χ (fun _ => 1) :=
    fun g => ⟨g.property, g.property, (mul_one _).symm⟩
  exact ⟨fun χ hχ => ⟨χ, hχ, h χ⟩, fun χ hχ => ⟨χ, hχ, h χ⟩⟩

private theorem characterAgreesOn_trans {χ : H →* ℂˣ} {η : K →* ℂˣ} {ζ : J →* ℂˣ}
    {t u : G → ℂ} (hχ : characterAgreesOn H χ η t) (hη : characterAgreesOn K η ζ u) :
    characterAgreesOn H χ ζ (fun g => u g * t g) := by
  intro g
  obtain ⟨hH, hK, ha⟩ := hχ g
  obtain ⟨_, hJ, hb⟩ := hη ⟨g, hK⟩
  exact ⟨hH, hJ, by rw [ha, hb, mul_assoc]⟩

private theorem CharacterSetTwistCorrespondence.trans
    {C : Set (H →* ℂˣ)} {D : Set (K →* ℂˣ)} {E : Set (J →* ℂˣ)} {t u : G → ℂ}
    (hCD : CharacterSetTwistCorrespondence C D t) (hDE : CharacterSetTwistCorrespondence D E u) :
    CharacterSetTwistCorrespondence C E (fun g => u g * t g) := by
  constructor
  · intro χ hχ
    obtain ⟨η, hη, hχη⟩ := hCD.1 χ hχ
    obtain ⟨ζ, hζ, hηζ⟩ := hDE.1 η hη
    exact ⟨ζ, hζ, characterAgreesOn_trans hχη hηζ⟩
  · intro ζ hζ
    obtain ⟨η, hη, hηζ⟩ := hDE.2 ζ hζ
    obtain ⟨χ, hχ, hχη⟩ := hCD.2 η hη
    exact ⟨χ, hχ, characterAgreesOn_trans hχη hηζ⟩

private theorem characterAgreesOn_one_of_domain_eq (h : H = K) (η : K →* ℂˣ) :
    characterAgreesOn H (Eq.ndrec (motive := fun L : Subgroup G => L →* ℂˣ) η h.symm)
      η (fun _ => 1) := by
  cases h
  intro g
  exact ⟨g.property, g.property, (mul_one _).symm⟩

private theorem characterAgreesOn_of_inverse_twist (h : H = K) {χ : H →* ℂˣ} {η : K →* ℂˣ}
    {twist : G → ℂ} (ht : characterAgreesOn K η χ (fun g => (twist g)⁻¹)) :
    characterAgreesOn H χ η twist := by
  intro g
  obtain ⟨hK, hH, he⟩ := ht ⟨g, h ▸ g.property⟩
  change (η ⟨g, hK⟩ : ℂ) = (χ ⟨g, hH⟩ : ℂ) * (twist g)⁻¹ at he
  refine ⟨hH, hK, ?_⟩
  have hz : twist g ≠ 0 := by
    intro hg
    rw [hg, inv_zero, mul_zero] at he
    exact Units.ne_zero _ he
  calc
    (χ ⟨g, hH⟩ : ℂ) = ((χ ⟨g, hH⟩ : ℂ) * (twist g)⁻¹) * twist g := by
      rw [mul_assoc, inv_mul_cancel₀ hz, mul_one]
    _ = (η ⟨g, hK⟩ : ℂ) * twist g := by rw [← he]

end CharacterSets

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ
local notation "Hc(" S "," q "," m ")" => simpleHGroup (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q) (m + 1)
local notation "Cc(" ψ "," S "," q "," m ")" => simpleCharacters ψ (Stratum.chain S) (Stratum.n S)
  (Stratum.b S) (Stratum.DefiningSequenceChoice.tail q) m

namespace Stratum

private theorem stabilizer_eq_of_order_eq {L M : LatticeChain 𝒪[F] F V} (h : L.order = M.order) :
    L.stabilizer = M.stabilizer := by
  rw [← (normalizer F V L).2.2.1 0, ← (normalizer F V M).2.2.1 0,
    LatticeChain.unitFiltration_eq_of_order_eq h]

/-- Represent a stratum using a chain with the same hereditary order. -/
def withChainAndLevel (S : Stratum 𝒪[F] F V) (L : LatticeChain 𝒪[F] F V) (n : ℤ)
    (hL : L.order = S.chain.order) (hn : n = S.n) : Stratum 𝒪[F] F V where
  chain := L
  n := n
  r := S.r
  b := S.b
  r_lt_n := hn.symm ▸ S.r_lt_n
  valuation_ge := by
    rw [hn, LatticeChain.valuation, LatticeChain.endFiltration_eq_of_order_eq hL]
    exact S.valuation_ge

private theorem isPure_withChainAndLevel (S : Stratum 𝒪[F] F V) (L : LatticeChain 𝒪[F] F V)
    (n : ℤ) (hL : L.order = S.chain.order) (hn : n = S.n) (hS : S.IsPure) :
    (S.withChainAndLevel L n hL hn).IsPure := by
  refine ⟨?_, ?_⟩
  · obtain ⟨hE, hnormalize⟩ := hS.1
    refine ⟨hE, fun a => ?_⟩
    change _ ∈ L.stabilizer
    rw [stabilizer_eq_of_order_eq hL]
    exact hnormalize a
  · change L.valuation S.b = (-n : WithTop ℤ)
    rw [hn, LatticeChain.valuation, LatticeChain.endFiltration_eq_of_order_eq hL]
    exact hS.2

/-- Replacing the chain by one of the same order preserves simplicity. -/
theorem isSimple_withChainAndLevel (S : Stratum 𝒪[F] F V) (L : LatticeChain 𝒪[F] F V)
    (n : ℤ) (hL : L.order = S.chain.order) (hn : n = S.n) (hS : S.IsSimple) :
    (S.withChainAndLevel L n hL hn).IsSimple := by
  refine ⟨isPure_withChainAndLevel S L n hL hn hS.1, ?_⟩
  change criticalExponent L S.b < ((-S.r : ℤ) : WithBot ℤ)
  rw [LatticeChain.criticalExponent_eq_of_order_eq hL]
  exact hS.2

/-- The same terms form a defining sequence for the new presentation. -/
def DefiningSequenceChoice.withChainAndLevel {S : Stratum 𝒪[F] F V} (q : S.DefiningSequenceChoice)
    (L : LatticeChain 𝒪[F] F V) (n : ℤ) (hL : L.order = S.chain.order) (hn : n = S.n) :
    (S.withChainAndLevel L n hL hn).DefiningSequenceChoice := by
  obtain ⟨hPure, hTerms, hFirst, hDepth, hMono, hStep, hLast, hDerived⟩ := q.isDefiningSequence
  refine ⟨q.steps, q.terms, ⟨isPure_withChainAndLevel S L n hL hn hPure, ?_, ?_, hDepth,
    hMono, ?_, ?_, hDerived⟩, q.firstElement⟩
  · intro i
    exact ⟨(hTerms i).1.trans hL.symm, (hTerms i).2.1.trans hn.symm, (hTerms i).2.2⟩
  · unfold Equivalent coset at hFirst ⊢
    simpa only [Stratum.withChainAndLevel, LatticeChain.endFiltration_eq_of_order_eq hL] using hFirst
  · intro i
    simpa only [Stratum.withChainAndLevel, LatticeChain.criticalExponent_eq_of_order_eq hL,
      LatticeChain.endFiltration_eq_of_order_eq hL] using hStep i
  · simpa only [Stratum.withChainAndLevel, LatticeChain.criticalExponent_eq_of_order_eq hL, hn] using hLast

end Stratum

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem finiteCriticalDepth_eq_of_criticalExponent_eq (L : LatticeChain 𝒪[F] F V)
    (n : ℤ) (b : A) (r : ℤ) (h : criticalExponent L b = ((-r : ℤ) : WithBot ℤ)) :
    finiteCriticalDepth L n b = r := by
  simp [finiteCriticalDepth, simpleCriticalDepth, h]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem terminal_depth {S : Stratum 𝒪[F] F V} (q : S.DefiningSequenceChoice)
    (hq : q.steps = 0) : finiteCriticalDepth S.chain S.n S.b = S.n := by
  have hj : Fin.last q.steps = 0 := Fin.ext hq
  have hl := q.isDefiningSequence.2.2.2.2.2.2.1
  rw [hj, q.firstElement] at hl
  rcases hl with h | h
  · exact finiteCriticalDepth_eq_of_criticalExponent_eq S.chain S.n S.b S.n h
  · simp [finiteCriticalDepth, simpleCriticalDepth, h]

private theorem tail_first_suffix {S : Stratum 𝒪[F] F V} (q : S.DefiningSequenceChoice)
    (h : 0 < q.steps) :
    q.tail = (q.terms (Fin.succ ⟨0, h⟩)).b :: (q.suffix (Fin.succ ⟨0, h⟩)).tail := by
  rw [q.tail_suffix]
  apply List.ext_getElem
  · simp only [List.length_cons, List.length_drop, Stratum.DefiningSequenceChoice.tail,
      List.length_ofFn, Fin.val_succ]
    omega
  · intro j hj hj'
    cases j with
    | zero => simp [Stratum.DefiningSequenceChoice.tail]
    | succ j =>
      simp only [List.getElem_cons_succ, List.getElem_drop, Stratum.DefiningSequenceChoice.tail,
        List.getElem_ofFn]
      apply congrArg (fun a : Fin (q.steps + 1) => (q.terms a).b)
      apply Fin.ext
      simp [Nat.add_comm]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem simpleHGroup_eq_of_layer_eq (L : LatticeChain 𝒪[F] F V) (n : ℤ)
    (β γ : A) (tail tail' : List A) (k : ℕ)
    (h : simpleHLayer L n β tail k = simpleHLayer L n γ tail' k) :
    simpleHGroup L n β tail k = simpleHGroup L n γ tail' k := by
  have memLayer (b : A) (bs : List A) (g : G) (hg : g ∈ L.unitFiltration k) :
      (g : A) ∈ simpleHLattice L n b bs ↔ (g : A) - 1 ∈ simpleHLayer L n b bs k := by
    have hone : (1 : A) ∈ simpleHLattice L n b bs := by
      have hc : (1 : A) ∈ centralizerLattice L b 0 :=
        ⟨L.mem_order_iff_mem_endFiltration.mp (one_mem L.order), by simp [adjointMap]⟩
      cases bs <;> exact Submodule.mem_sup_left hc
    exact ⟨fun hg' => ⟨sub_mem hg' hone, hg.2.2⟩,
      fun hg' => by simpa using add_mem hg'.1 hone⟩
  unfold simpleHGroup
  congr 1
  ext g
  change (g ∈ L.unitFiltration k ∧ (g : A) ∈ simpleHLattice L n β tail) ↔
    (g ∈ L.unitFiltration k ∧ (g : A) ∈ simpleHLattice L n γ tail')
  refine and_congr_right fun hg => ?_
  rw [memLayer β tail g hg, memLayer γ tail' g hg, h]

private theorem elementCharacter_eq_one_on_unitFiltration (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    (L : LatticeChain 𝒪[F] F V) (m : ℕ) {b : A}
    (hb : b ∈ L.endFiltration (-(m : ℤ))) {g : G} (hg : g ∈ L.unitFiltration (m + 1)) :
    elementCharacter (traceCharacter ψF) b g = 1 := by
  have hd := (additiveDuality F V L ψF hψ.1 hψ.2).1 ((m : ℤ) + 1)
  have ha : b ∈ additiveDual (traceCharacter ψF) (L.endFiltration ((m : ℤ) + 1) : Set A) := by
    rw [hd, show (1 : ℤ) - (m + 1) = -m by omega]
    exact hb
  exact ha ((g : A) - 1) hg.2.2

private theorem oneStep_twist (hlattices : SimpleStratumLatticePropertiesStatement.{uF, uV})
    (hrestriction : SimpleCharacterRestrictionStatement.{uF, uV})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    {S T : Stratum 𝒪[F] F V} (q : S.DefiningSequenceChoice) (q' : T.DefiningSequenceChoice)
    (hS : S.IsSimple) (hrS : 0 ≤ S.r) (hST : S.IsCriticalApproximation T)
    (hchain : T.chain = S.chain) (htail : q.tail = T.b :: q'.tail)
    (m : ℕ) (hm : T.r / 2 ≤ (m : ℤ)) :
    Hc(S, q, m) = Hc(T, q', m) ∧
      CharacterSetTwistCorrespondence (Cc(ψF, S, q, m)) (Cc(ψF, T, q', m))
        (elementCharacter (traceCharacter ψF) (S.b - T.b)) := by
  have hr := finiteCriticalDepth_eq_of_criticalExponent_eq S.chain S.n S.b T.r hST.2.2.2.1
  let S₀ := S.atDepthZero (hrS.trans_lt S.r_lt_n)
  let q₀ := q.atDepthZero hrS
  have hS₀ : S₀.IsSimple := Stratum.isSimple_atDepthZero hS hrS
  have hST₀ : S₀.IsCriticalApproximation T := hST
  by_cases hmr : (m : ℤ) < T.r
  · obtain ⟨hdom, e, he⟩ := (hrestriction F V ψF hψ S₀ rfl hS₀ q₀).2.2.1 T hST₀ q' m
      (hr.symm ▸ hm) (hr.symm ▸ hmr)
    refine ⟨hdom, ?_, ?_⟩
    · intro χ hχ
      let χ₀ : Cc(ψF, S, q, m) := ⟨χ, hχ⟩
      exact ⟨(e χ₀).val, (e χ₀).property, characterAgreesOn_of_inverse_twist hdom (he χ₀)⟩
    · intro η hη
      let η₀ : Cc(ψF, T, q', m) := ⟨η, hη⟩
      refine ⟨(e.symm η₀).val, (e.symm η₀).property, ?_⟩
      have ha := he (e.symm η₀)
      rw [e.apply_symm_apply] at ha
      exact characterAgreesOn_of_inverse_twist hdom ha
  · have hcut : simpleHCutoff (finiteCriticalDepth S.chain S.n S.b) ≤ ((m + 1 : ℕ) : ℤ) := by
      rw [hr]
      unfold simpleHCutoff
      omega
    have hlayer := ((hlattices F V S₀ rfl hS₀ q₀).2.2.1 T hST₀ q').1 (m + 1) hcut
    have hn := hST.2.1
    have hdom : Hc(S, q, m) = Hc(T, q', m) := by
      rw [hchain, hn]
      exact simpleHGroup_eq_of_layer_eq S.chain S.n S.b T.b q.tail q'.tail (m + 1) hlayer
    have htriv (g : Hc(S, q, m)) : elementCharacter (traceCharacter ψF) (S.b - T.b) g = 1 := by
      have hb : S.b - T.b ∈ S.chain.endFiltration (-T.r) := by
        simpa only [neg_sub] using neg_mem hST.2.2.2.2
      exact elementCharacter_eq_one_on_unitFiltration ψF hψ S.chain m
        (S.chain.endFiltration_antitone (by omega) hb)
        (simpleHGroup_le_unitFiltration S.chain S.n S.b q.tail (m + 1) g.property)
    rw [hchain, hn, htail] at hdom ⊢
    rw [htail] at htriv
    have hmr' : ¬ (m : ℤ) < finiteCriticalDepth S.chain S.n S.b := by rwa [hr]
    simp only [simpleCharacters, ite_eq_right hmr']
    refine ⟨hdom, ?_, ?_⟩
    · rintro χ ⟨η, hη, _, ha⟩
      refine ⟨η, hη, fun g => ?_⟩
      simpa only [htriv g] using ha g
    · intro η hη
      have ha := characterAgreesOn_one_of_domain_eq hdom η
      refine ⟨_, ⟨η, hη, hdom, ha⟩, fun g => ?_⟩
      simpa only [htriv g] using ha g

/-- A core at depth `m` has the original order, level and character domain. Its
cutoff lies above `m`, and its character set gives the original set by the additive twist. -/
structure SimpleCharacterCore (ψF : AddChar F ℂ) (S : Stratum 𝒪[F] F V)
    (q : S.DefiningSequenceChoice) (m : ℕ) where
  stratum : Stratum 𝒪[F] F V
  sequence : stratum.DefiningSequenceChoice
  chain_eq : stratum.chain = S.chain
  level_eq : stratum.n = S.n
  depth_le : S.r ≤ stratum.r
  congruence : S.b - stratum.b ∈ S.chain.endFiltration (-stratum.r)
  isSimple : stratum.IsSimple
  below_cutoff : (m : ℤ) < finiteCriticalDepth stratum.chain stratum.n stratum.b / 2
  domain_eq : Hc(S, q, m) = Hc(stratum, sequence, m)
  twist : CharacterSetTwistCorrespondence (Cc(ψF, S, q, m)) (Cc(ψF, stratum, sequence, m))
    (elementCharacter (traceCharacter ψF) (S.b - stratum.b))

/-- The first defining-sequence term whose cutoff lies above `m` gives a core twist.
The input lattice comparison and critical-approximation twist are the clauses of (3.1.9) and (3.3.18). -/
theorem exists_simpleCharacterCore_with_depth_bound
    (hlattices : SimpleStratumLatticePropertiesStatement.{uF, uV})
    (hrestriction : SimpleCharacterRestrictionStatement.{uF, uV})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    {S : Stratum 𝒪[F] F V} (q : S.DefiningSequenceChoice) (hS : S.IsSimple) (hrS : 0 ≤ S.r)
    (m : ℕ) (hm : (m : ℤ) < S.n / 2) :
    ∃ core : SimpleCharacterCore ψF S q m, core.stratum.r ≤ max S.r (2 * (m : ℤ) + 1) := by
  suffices ∀ k {S : Stratum 𝒪[F] F V} (q : S.DefiningSequenceChoice), q.steps = k →
    S.IsSimple → 0 ≤ S.r → (m : ℤ) < S.n / 2 →
      ∃ core : SimpleCharacterCore ψF S q m, core.stratum.r ≤ max S.r (2 * (m : ℤ) + 1) from
    this q.steps q rfl hS hrS hm
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro S q hk hS hrS hm
    by_cases hcore : (m : ℤ) < finiteCriticalDepth S.chain S.n S.b / 2
    · refine ⟨⟨S, q, rfl, rfl, le_rfl, by simp, hS, hcore, rfl, ?_⟩, le_max_left _ _⟩
      have ht : elementCharacter (traceCharacter ψF) (S.b - S.b) = (fun _ : G => 1) := by
        funext g
        simp [elementCharacter]
      rw [ht]
      exact characterSetTwistCorrespondence_one (Cc(ψF, S, q, m))
    have hpos : 0 < q.steps := by
      by_contra! h
      rw [terminal_depth q (by omega)] at hcore
      exact hcore hm
    let i : Fin q.steps := ⟨0, hpos⟩
    let U := q.terms i.succ
    have ht := q.isDefiningSequence.2.1 i.succ
    let T := U.withChainAndLevel S.chain S.n ht.1.symm ht.2.1.symm
    let q' := (q.suffix i.succ).withChainAndLevel S.chain S.n ht.1.symm ht.2.1.symm
    have hT : T.IsSimple := U.isSimple_withChainAndLevel S.chain S.n ht.1.symm ht.2.1.symm ht.2.2
    have hST : S.IsCriticalApproximation T := by
      have h := q.isDefiningSequence.2.2.2.2.2.1 i
      have hi : i.castSucc = 0 := Fin.ext rfl
      rw [hi, q.firstElement] at h
      exact ⟨rfl, rfl, hT, h⟩
    have hrST : S.r < T.r := by
      have h := q.isDefiningSequence.2.2.2.2.1 (Fin.castSucc_lt_succ (i := i))
      have hi : i.castSucc = 0 := Fin.ext rfl
      change (q.terms i.castSucc).r < (q.terms i.succ).r at h
      rw [hi, q.isDefiningSequence.2.2.2.1] at h
      exact h
    have hcut : T.r / 2 ≤ (m : ℤ) := by
      rw [finiteCriticalDepth_eq_of_criticalExponent_eq S.chain S.n S.b T.r hST.2.2.2.1] at hcore
      exact le_of_not_gt hcore
    obtain ⟨hdom, htwist⟩ := oneStep_twist hlattices hrestriction ψF hψ q q' hS hrS hST rfl
      (tail_first_suffix q hpos) m hcut
    have hsteps : q'.steps < k := by
      change q.steps - 1 < k
      omega
    obtain ⟨core, hcoreBound⟩ := ih q'.steps hsteps q' rfl hT (hrS.trans hrST.le) hm
    have hTBound : T.r ≤ 2 * (m : ℤ) + 1 := by omega
    have hbound : core.stratum.r ≤ max S.r (2 * (m : ℤ) + 1) := by
      refine hcoreBound.trans ?_
      rw [max_eq_right hTBound]
      exact le_max_right _ _
    have hc : S.b - T.b ∈ S.chain.endFiltration (-T.r) := by
      simpa only [neg_sub] using neg_mem hST.2.2.2.2
    have hc' : T.b - core.stratum.b ∈ S.chain.endFiltration (-core.stratum.r) := core.congruence
    have hcongr : S.b - core.stratum.b ∈ S.chain.endFiltration (-core.stratum.r) := by
      simpa only [sub_add_sub_cancel] using
        add_mem (S.chain.endFiltration_antitone (neg_le_neg core.depth_le) hc) hc'
    refine ⟨⟨core.stratum, core.sequence, core.chain_eq, core.level_eq, hrST.le.trans core.depth_le,
      hcongr, core.isSimple, core.below_cutoff, hdom.trans core.domain_eq, ?_⟩, hbound⟩
    have htwistEq (g : G) : elementCharacter (traceCharacter ψF) (T.b - core.stratum.b) g *
        elementCharacter (traceCharacter ψF) (S.b - T.b) g =
          elementCharacter (traceCharacter ψF) (S.b - core.stratum.b) g := by
      simp only [elementCharacter_apply, ← AddChar.map_add_eq_mul, ← add_mul,
        show T.b - core.stratum.b + (S.b - T.b) = S.b - core.stratum.b by abel]
    rw [← funext htwistEq]
    exact htwist.trans core.twist

/-- Each depth below half the level has a core approximation. -/
theorem exists_simpleCharacterCore (hlattices : SimpleStratumLatticePropertiesStatement.{uF, uV})
    (hrestriction : SimpleCharacterRestrictionStatement.{uF, uV})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    {S : Stratum 𝒪[F] F V} (q : S.DefiningSequenceChoice) (hS : S.IsSimple) (hrS : 0 ≤ S.r)
    (m : ℕ) (hm : (m : ℤ) < S.n / 2) : Nonempty (SimpleCharacterCore ψF S q m) :=
  (exists_simpleCharacterCore_with_depth_bound hlattices hrestriction ψF hψ q hS hrS m hm).elim
    (fun core _ => ⟨core⟩)

end Langlands.BushnellKutzko
