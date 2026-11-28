import Langlands.BushnellKutzko.SimpleCharacterChoiceStatement
import Langlands.BushnellKutzko.SimpleCharacterIntertwiningProof
import Langlands.BushnellKutzko.SimpleCharacterRelativeDeterminant
import Langlands.BushnellKutzko.SimpleCharacterRestrictionHigh
import Langlands.BushnellKutzko.SimpleCharacterSequence
import Langlands.BushnellKutzko.IntertwinedUnitCharacter
import Langlands.BushnellKutzko.SimpleIntertwiningProof
import Langlands.BushnellKutzko.SimpleStratumLatticePropertiesProof
import Langlands.BushnellKutzko.StratumEquivalenceProof

/-! # Change of approximants in the simple-character recursion -/

open ValuativeRel
open scoped Pointwise

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV uG

section CharacterValues

variable {G : Type uG} [Group G] {K H H' : Subgroup G}

private theorem characterAgreesOn_of_le (h : K ≤ H) (h' : K ≤ H')
    (θ : H →* ℂˣ) (θ' : H' →* ℂˣ) (f : G → ℂ) :
    characterAgreesOn K θ θ' f ↔
      ∀ g : K, (θ ⟨g, h g.property⟩ : ℂ) = (θ' ⟨g, h' g.property⟩ : ℂ) * f g := by
  constructor
  · intro hf g
    obtain ⟨_, _, hv⟩ := hf g
    exact hv
  · exact fun hf g => ⟨h g.property, h' g.property, hf g⟩

end CharacterValues

section Strata

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ
local notation "Str" => Stratum 𝒪[F] F V
local notation "Chain" => LatticeChain 𝒪[F] F V

open StratumEquivalence

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem simpleCriticalDepth_coe_lt_iff (L : Chain) (b : A) (t : ℤ) :
    (t : WithTop ℤ) < simpleCriticalDepth L b ↔
      criticalExponent L b < ((-t : ℤ) : WithBot ℤ) := by
  unfold simpleCriticalDepth
  cases criticalExponent L b with
  | bot => simp
  | coe k => simpa only [simpleCriticalDepth, WithTop.coe_lt_coe, WithBot.coe_lt_coe] using
      (show t < -k ↔ k < -t by omega)

private def atDepth (S : Str) (r : ℤ) (hr : r < S.n) : Str :=
  { S with r := r, r_lt_n := hr }

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem atDepth_isSimple {S : Str} {r : ℤ} (hr : r < S.n) (hS : S.IsPure)
    (hcrit : (r : WithTop ℤ) < simpleCriticalDepth S.chain S.b) :
    (atDepth S r hr).IsSimple :=
  ⟨hS, (simpleCriticalDepth_coe_lt_iff _ _ _).1 hcrit⟩

private theorem atDepth_equivalent {S T : Str} {r : ℤ} (hrS : r < S.n) (hrT : r < T.n)
    (horder : S.chain.order = T.chain.order) (hb : T.b - S.b ∈ S.chain.endFiltration (-r)) :
    (atDepth S r hrS).Equivalent (atDepth T r hrT) := by
  ext x
  change x - S.b ∈ S.chain.endFiltration (-r) ↔ x - T.b ∈ T.chain.endFiltration (-r)
  rw [← LatticeChain.endFiltration_eq_of_order_eq horder]
  constructor
  · intro hx
    convert sub_mem hx hb using 1
    abel
  · intro hx
    convert add_mem hx hb using 1
    abel

private def choiceFromTerms (S : Str) (s : ℕ) (f : Fin (s + 1) → Str)
    (h : S.IsDefiningSequence f) (hb : (f 0).b = S.b) : S.DefiningSequenceChoice :=
  ⟨s, f, h, hb⟩

private theorem valuation_eq_of_order {L M : Chain} (ho : L.order = M.order) (b : A) :
    L.valuation b = M.valuation b := by
  simp only [LatticeChain.valuation, LatticeChain.endFiltration_eq_of_order_eq ho]

private theorem stabilizer_eq_of_order {L M : Chain} (ho : L.order = M.order) :
    L.stabilizer = M.stabilizer := by
  ext g
  rw [(normalizer F V L).2.1 g, (normalizer F V M).2.1 g, ho]

private def stepStratum {S : Str} {s : ℕ} (f : Fin (s + 1 + 1) → Str)
    (h : S.IsDefiningSequence f) : Str :=
  let T := f (Fin.succ 0)
  let ht := h.2.1 (Fin.succ 0)
  { chain := S.chain
    n := S.n
    r := T.r
    b := T.b
    r_lt_n := ht.2.1 ▸ T.r_lt_n
    valuation_ge := by rw [← ht.2.1, ← valuation_eq_of_order ht.1]; exact T.valuation_ge }

private theorem stepStratum_isSimple {S : Str} {s : ℕ} {f : Fin (s + 1 + 1) → Str}
    (h : S.IsDefiningSequence f) : (stepStratum f h).IsSimple := by
  let T := f (Fin.succ 0)
  obtain ⟨ho, hn, ⟨⟨hF, hstab⟩, hv⟩, hc⟩ := h.2.1 (Fin.succ 0)
  refine ⟨⟨⟨hF, ?_⟩, ?_⟩, ?_⟩
  · let := hF.toField
    change ∀ a : (elementAlgebra T.b)ˣ, subfieldUnits F _ V a ∈ S.chain.stabilizer
    rw [← stabilizer_eq_of_order ho]
    exact hstab
  · change S.chain.valuation T.b = (-S.n : WithTop ℤ)
    rw [← valuation_eq_of_order ho, ← hn]
    exact hv
  · change criticalExponent S.chain T.b < ((-T.r : ℤ) : WithBot ℤ)
    rw [← criticalExponent_congr (LatticeChain.endFiltration_eq_of_order_eq ho)]
    exact hc

private def choiceDrop {S : Str} {s : ℕ} (f : Fin (s + 1 + 1) → Str)
    (h : S.IsDefiningSequence f) : (stepStratum f h).DefiningSequenceChoice := by
  have hs := stepStratum_isSimple h
  obtain ⟨_, hf, _, _, hmono, hsteps, hlast, hderived⟩ := h
  refine ⟨s, fun i => f i.succ, ⟨hs.1, ?_, ?_, rfl, ?_, ?_, ?_, ?_⟩, rfl⟩
  · exact fun i => hf i.succ
  · have hP := LatticeChain.endFiltration_eq_of_order_eq (hf (Fin.succ 0)).1
    ext x
    change x - (f (Fin.succ 0)).b ∈ (f (Fin.succ 0)).chain.endFiltration _ ↔
      x - (f (Fin.succ 0)).b ∈ S.chain.endFiltration _
    rw [hP]
    rfl
  · intro i j hij
    exact hmono (Fin.succ_lt_succ_iff.mpr hij)
  · intro i
    simpa only [stepStratum, Fin.succ_castSucc] using hsteps i.succ
  · simpa only [stepStratum, Fin.succ_last] using hlast
  · intro i
    simpa only [Fin.succ_castSucc] using hderived i.succ

private theorem choice_cons_tail {S : Str} {s : ℕ} {f : Fin (s + 1 + 1) → Str}
    (h : S.IsDefiningSequence f) (hb : (f 0).b = S.b) :
    (choiceFromTerms S (s + 1) f h hb).tail =
      (stepStratum f h).b :: (choiceDrop f h).tail := by
  simp only [Stratum.DefiningSequenceChoice.tail, choiceFromTerms, List.ofFn_succ, choiceDrop,
    stepStratum]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem choice_terminal {S : Str} {f : Fin (0 + 1) → Str}
    (h : S.IsDefiningSequence f) (hb : (f 0).b = S.b) :
    simpleCriticalDepth S.chain S.b = (S.n : WithTop ℤ) ∨
      simpleCriticalDepth S.chain S.b = ⊤ := by
  have hlast : Fin.last 0 = 0 := Fin.ext rfl
  rcases h.2.2.2.2.2.2.1 with h | h <;>
    rw [hlast, hb] at h <;>
    simp [simpleCriticalDepth, h]

private theorem choice_step {S : Str} {s : ℕ} {f : Fin (s + 1 + 1) → Str}
    (h : S.IsDefiningSequence f) (hb : (f 0).b = S.b) :
    let T := stepStratum f h
    S.r < T.r ∧ simpleCriticalDepth S.chain S.b = (T.r : WithTop ℤ) ∧
      T.b - S.b ∈ S.chain.endFiltration (-T.r) := by
  obtain ⟨_, _, _, hr, hmono, ht, _, _⟩ := h
  have hc := ht (0 : Fin (s + 1))
  rw [show (0 : Fin (s + 1)).castSucc = 0 from rfl, hb] at hc
  have hlt : (f 0).r < (f (Fin.succ 0)).r := hmono (Fin.succ_pos _)
  rw [hr] at hlt
  exact ⟨hlt, by simp [simpleCriticalDepth, hc.1, stepStratum], hc.2⟩

private def choiceAtDepth {S : Str} (q : S.DefiningSequenceChoice) {d : ℤ}
    (hd : d < S.n) (hc : (d : WithTop ℤ) < simpleCriticalDepth S.chain S.b) :
    (atDepth S d hd).DefiningSequenceChoice := by
  classical
  let S₀ := atDepth S d hd
  let f := fun i => if i = 0 then S₀ else q.terms i
  obtain ⟨hPure, hf, _, _, hmono, hstep, hlast, hderived⟩ := q.isDefiningSequence
  have hb (i) : (f i).b = (q.terms i).b := by
    by_cases hi : i = 0
    · subst i
      simp [f, S₀, atDepth, q.firstElement]
    · simp [f, hi]
  have hf₀ : f 0 = S₀ := ite_eq_left rfl
  refine ⟨q.steps, f, ⟨hPure, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i
    by_cases hi : i = 0
    · subst i
      rw [hf₀]
      exact ⟨rfl, rfl, atDepth_isSimple _ hPure hc⟩
    · simpa only [f, ite_eq_right hi, atDepth] using hf i
  · rw [hf₀]; rfl
  · rw [hf₀]
  · intro i j hij
    have hj : j ≠ 0 := ne_of_gt ((Fin.zero_le i).trans_lt hij)
    have hii : ((q.terms i).r) < (q.terms j).r := hmono hij
    by_cases hi : i = 0
    · subst i
      let j₀ : Fin q.steps := ⟨0, by
        have hlt : 0 < j.val := by exact (Fin.pos_iff_ne_zero).2 hj
        omega⟩
      have hcrit := (hstep j₀).1
      have hj₀ : j₀.castSucc = 0 := Fin.ext rfl
      rw [hj₀, q.firstElement] at hcrit
      have hLt : d < (q.terms j₀.succ).r := by
        have he : simpleCriticalDepth S.chain S.b = (((q.terms j₀.succ).r : ℤ) : WithTop ℤ) := by
          simp [simpleCriticalDepth, hcrit]
        exact WithTop.coe_lt_coe.mp (he ▸ hc)
      have hj' : j₀.succ ≤ j := by
        change 1 ≤ j.val
        exact (Fin.pos_iff_ne_zero).2 hj
      simpa only [f, ite_eq_left rfl, ite_eq_right hj, S₀, atDepth] using
        hLt.trans_le (hmono.monotone hj')
    · simpa only [f, ite_eq_right hi, ite_eq_right hj] using hii
  · intro i
    have hi : i.succ ≠ 0 := Fin.succ_ne_zero i
    simpa only [hb, atDepth, show (f i.succ).r = (q.terms i.succ).r by simp [f, hi]] using hstep i
  · simpa only [hb, atDepth] using hlast
  · intro i
    rw [hb, show f i.succ = q.terms i.succ from ite_eq_right (Fin.succ_ne_zero i)]
    exact hderived i
  · rw [hf₀]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem choiceAtDepth_tail {S : Str} (q : S.DefiningSequenceChoice) {d : ℤ}
    (hd : d < S.n) (hc : (d : WithTop ℤ) < simpleCriticalDepth S.chain S.b) :
    (choiceAtDepth q hd hc).tail = q.tail := by
  change (List.ofFn fun i : Fin q.steps =>
    ((if i.succ = 0 then atDepth S d hd else q.terms i.succ) : Str).b) = q.tail
  simp [Stratum.DefiningSequenceChoice.tail, Fin.succ_ne_zero]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem simpleHLattice_congr {L M : Chain} (hP : L.endFiltration = M.endFiltration)
    (n : ℤ) (b : A) (tail : List A) : simpleHLattice L n b tail = simpleHLattice M n b tail := by
  induction tail generalizing b with
  | nil => simp only [simpleHLattice, simpleStratumLattices, centralizerLattice_congr hP, hP]
  | cons a tail ih =>
    simp only [simpleHLattice, simpleStratumLattices, centralizerLattice_congr hP, hP,
      finiteCriticalDepth, simpleCriticalDepth, criticalExponent_congr hP]
    rw [show (simpleStratumLattices L n a tail).1 = (simpleStratumLattices M n a tail).1 from ih a]

private theorem simpleHGroup_eq_of_layer {L M : Chain} {n : ℤ} {b c : A} {tail tail' : List A}
    {k : ℕ} (horder : L.order = M.order)
    (hlayer : simpleHLayer L n b tail k = simpleHLayer M n c tail' k) :
    simpleHGroup L n b tail k = simpleHGroup M n c tail' k := by
  have hcarrier (P : Chain) (β : A) (u : List A) (g : G) :
      g ∈ simpleHCarrier P n β u k ↔
        g ∈ P.unitFiltration k ∧ (g : A) - 1 ∈ simpleHLayer P n β u k := by
    change _ ∧ _ ↔ _ ∧ _
    refine and_congr_right fun hg => ?_
    have h₁ := one_mem_simpleHLattice P n β u
    constructor
    · exact fun h => ⟨sub_mem h h₁, hg.2.2⟩
    · intro h
      simpa only [sub_add_cancel] using add_mem h.1 h₁
  unfold simpleHGroup
  congr 1
  ext g
  rw [hcarrier, hcarrier, LatticeChain.unitFiltration_eq_of_order_eq horder, hlayer]

private theorem simpleHGroup_eq_at_equivalence (hL : SimpleStratumLatticePropertiesStatement.{uF,uV})
    {S T : Str} (hS : S.IsSimple) (hS₀ : 0 ≤ S.r) (hT : T.IsSimple)
    (q : S.DefiningSequenceChoice) (q' : T.DefiningSequenceChoice)
    (hO : S.chain.order = T.chain.order) (hn : S.n = T.n)
    (hc : (T.r : WithTop ℤ) < simpleCriticalDepth S.chain S.b)
    (hdiff : T.b - S.b ∈ S.chain.endFiltration (-T.r))
    {m : ℕ} (hm : T.r / 2 ≤ (m : ℤ)) :
    simpleHGroup S.chain S.n S.b q.tail (m + 1) =
      simpleHGroup T.chain T.n T.b q'.tail (m + 1) := by
  let S₀ := atDepth S 0 (hS₀.trans_lt S.r_lt_n)
  have hcrit : (0 : WithTop ℤ) < simpleCriticalDepth S.chain S.b :=
    lt_of_le_of_lt (WithTop.coe_le_coe.mpr hS₀) ((simpleCriticalDepth_coe_lt_iff _ _ _).2 hS.2)
  have hS₀simple : S₀.IsSimple := atDepth_isSimple _ hS.1 hcrit
  let q₀ := choiceAtDepth q (hS₀.trans_lt S.r_lt_n) hcrit
  have hPeq := LatticeChain.endFiltration_eq_of_order_eq hO
  have hk : (if simpleCriticalDepth S.chain S.b = ⊤ then 0 else
      max 0 (T.r + 1 - simpleJCutoff (finiteCriticalDepth S.chain S.n S.b))) ≤ ((m + 1 : ℕ) : ℤ) := by
    cases h : simpleCriticalDepth S.chain S.b with
    | top => simp; omega
    | coe r =>
      have hlr : T.r < r := WithTop.coe_lt_coe.mp (h ▸ hc)
      simp [h, finiteCriticalDepth, simpleJCutoff]
      omega
  have hclause := (hL F V S₀ rfl hS₀simple q₀).2.2.2.2.2 T hO.symm hn.symm hT hc hdiff q'
  have hLayer := (hclause.1 (m + 1) hk).symm
  have htail : q₀.tail = q.tail := choiceAtDepth_tail _ _ _
  rw [htail] at hLayer
  change simpleHLayer S.chain S.n S.b q.tail (m + 1) =
    simpleHLayer S.chain S.n T.b q'.tail (m + 1) at hLayer
  have hLayer' : simpleHLayer S.chain S.n S.b q.tail (m + 1) =
      simpleHLayer T.chain S.n T.b q'.tail (m + 1) := by
    exact hLayer.trans (by simp only [simpleHLayer, simpleHLattice_congr hPeq, hPeq])
  have hg := simpleHGroup_eq_of_layer hO hLayer'
  rw [← hn]
  exact hg

private theorem step_group_eq (hL : SimpleStratumLatticePropertiesStatement.{uF,uV})
    {S : Str} (hS : S.IsSimple) (hS₀ : 0 ≤ S.r) {s : ℕ} {f : Fin (s + 1 + 1) → Str}
    (h : S.IsDefiningSequence f) (hb : (f 0).b = S.b) {m : ℕ}
    (hm : (stepStratum f h).r / 2 ≤ (m : ℤ)) :
    simpleHGroup S.chain S.n S.b (choiceFromTerms S (s + 1) f h hb).tail (m + 1) =
      simpleHGroup S.chain S.n (stepStratum f h).b (choiceDrop f h).tail (m + 1) := by
  let S₀ := atDepth S 0 (hS₀.trans_lt S.r_lt_n)
  let T := stepStratum f h
  let q := choiceFromTerms S (s + 1) f h hb
  have hcrit : (0 : WithTop ℤ) < simpleCriticalDepth S.chain S.b :=
    lt_of_le_of_lt (WithTop.coe_le_coe.mpr hS₀) ((simpleCriticalDepth_coe_lt_iff _ _ _).2 hS.2)
  have hS₀simple : S₀.IsSimple := atDepth_isSimple _ hS.1 hcrit
  let q₀ := choiceAtDepth q (hS₀.trans_lt S.r_lt_n) hcrit
  have htail : q₀.tail = q.tail := choiceAtDepth_tail _ _ _
  have hstep := choice_step h hb
  have hce : criticalExponent S.chain S.b = ((-T.r : ℤ) : WithBot ℤ) := by
    have hc := h.2.2.2.2.2.1 (0 : Fin (s + 1))
    rw [show (0 : Fin (s + 1)).castSucc = 0 from rfl, hb] at hc
    exact hc.1
  have hApp : S₀.IsCriticalApproximation T := ⟨rfl, rfl, stepStratum_isSimple h, hce, hstep.2.2⟩
  have hm' : simpleHCutoff (finiteCriticalDepth S₀.chain S₀.n S₀.b) ≤ ((m + 1 : ℕ) : ℤ) := by
    change simpleHCutoff (finiteCriticalDepth S.chain S.n S.b) ≤ _
    rw [finiteCriticalDepth, hstep.2.1, WithTop.untopD_coe]
    simp only [simpleHCutoff, Nat.cast_add, Nat.cast_one]
    omega
  have hh := ((hL F V S₀ rfl hS₀simple q₀).2.2.1 T hApp (choiceDrop f h)).1 (m + 1) hm'
  rw [htail] at hh
  exact simpleHGroup_eq_of_layer rfl hh

private theorem exists_twisted_character (ψ : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψ)
    (L : Chain) {k : ℕ} {ℓ : ℤ} (hk : 1 ≤ (k : ℤ) + k - ℓ) {c : A}
    (hc : c ∈ L.endFiltration (-ℓ)) {H H' : Subgroup G} (h : H = H')
    (hU : H ≤ L.unitFiltration k) (θ : H →* ℂˣ) :
    ∃ θ' : H' →* ℂˣ, characterAgreesOn H' θ' θ (elementCharacter (traceCharacter ψ) c) := by
  let δ := elementCharacterHom L ψ hψ hc (by omega) (h.symm.le.trans hU)
  refine ⟨θ.comp (Subgroup.inclusion h.symm.le) * δ,
    (characterAgreesOn_of_le le_rfl h.symm.le _ _ _).2 ?_⟩
  intro g
  rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem agreesOn_twist_symm (ψ : AddChar F ℂ) {H H' : Subgroup G} (h : H = H')
    {θ : H →* ℂˣ} {θ' : H' →* ℂˣ} {c : A}
    (ha : characterAgreesOn H' θ' θ (elementCharacter (traceCharacter ψ) c)) :
    characterAgreesOn H θ θ' (elementCharacter (traceCharacter ψ) (-c)) := by
  intro g
  obtain ⟨h₁, h₂, hval⟩ := ha ⟨g, h.le g.property⟩
  refine ⟨h₂, h₁, ?_⟩
  rw [hval, mul_assoc, ← elementCharacter_add, add_neg_cancel]
  simp [elementCharacter_apply]

private theorem simpleDepth_eq {S T : Str} (hEq : S.Equivalent T) (hS : S.IsSimple)
    (hT : T.IsSimple) : simpleCriticalDepth S.chain S.b = simpleCriticalDepth T.chain T.b := by
  have := S.chain.finiteDimensional
  have he := (sup_eq_and_criticalExponent_eq_of_equivalent hEq hS hT).2
  simp only [simpleCriticalDepth, he]

private abbrev characterDomain (S : Str) (q : S.DefiningSequenceChoice) (m : ℕ) : Subgroup G :=
  simpleHGroup S.chain S.n S.b q.tail (m + 1)

private abbrev characterSet (ψ : AddChar F ℂ) (S : Str) (q : S.DefiningSequenceChoice) (m : ℕ) :
    Set (characterDomain S q m →* ℂˣ) := simpleCharacters ψ S.chain S.n S.b q.tail m

private abbrev twistLocalConditions (ψ : AddChar F ℂ) (S T : Str) (u v : List A) (m : ℕ) : Prop :=
  ∀ θ ∈ simpleCharacters ψ S.chain S.n S.b u m,
    ∀ θ' : simpleHGroup T.chain T.n T.b v (m + 1) →* ℂˣ,
      characterAgreesOn (simpleHGroup T.chain T.n T.b v (m + 1)) θ' θ
        (elementCharacter (traceCharacter ψ) (T.b - S.b)) →
      factorsThroughCentralizerDet T.b θ' ∧
        (relativeOrderNormalizer T.chain T.b : Set G) ⊆ characterNormalizer θ'

private abbrev twistMembership (ψ : AddChar F ℂ) (S T : Str) (u v : List A) (m : ℕ) : Prop :=
  ∀ θ ∈ simpleCharacters ψ S.chain S.n S.b u m,
    ∀ θ' : simpleHGroup T.chain T.n T.b v (m + 1) →* ℂˣ,
      characterAgreesOn (simpleHGroup T.chain T.n T.b v (m + 1)) θ' θ
        (elementCharacter (traceCharacter ψ) (T.b - S.b)) →
      θ' ∈ simpleCharacters ψ T.chain T.n T.b v m

/-- The local conditions to be recovered by the conjugation formula for the twisted character. -/
private def TwistPreservesLocalConditions (ψ : AddChar F ℂ) : Prop :=
  ∀ (S T : Str), S.IsSimple → T.IsSimple → 0 ≤ S.r → S.Equivalent T →
    ∀ (q : S.DefiningSequenceChoice) (q' : T.DefiningSequenceChoice) (m : ℕ),
      S.r / 2 ≤ (m : ℤ) → (m : ℤ) < S.n → ((m : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b →
      twistLocalConditions ψ S T q.tail q'.tail m

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem atDepth_self (S : Str) : atDepth S S.r S.r_lt_n = S := by
  cases S
  rfl

private theorem steps_equivalent {S T : Str} {s t : ℕ}
    {f : Fin (s + 1 + 1) → Str} {g : Fin (t + 1 + 1) → Str}
    (hf : S.IsDefiningSequence f) (hg : T.IsDefiningSequence g)
    (hb : (f 0).b = S.b) (hc : (g 0).b = T.b)
    (hEq : S.Equivalent T) (hS : S.IsSimple) (hT : T.IsSimple) :
    (stepStratum f hf).Equivalent (stepStratum g hg) := by
  let S₁ := stepStratum f hf
  let T₁ := stepStratum g hg
  have hS₁ := choice_step hf hb
  have hT₁ := choice_step hg hc
  have hdepth := simpleDepth_eq hEq hS hT
  have hr : S₁.r = T₁.r := WithTop.coe_injective (hS₁.2.1.symm.trans (hdepth.trans hT₁.2.1))
  have ho := order_eq_of_equivalent hEq
  have hP := LatticeChain.endFiltration_eq_of_order_eq ho
  have hδ : T.b - S.b ∈ S.chain.endFiltration (-S₁.r) := by
    have hlt : S.r < S₁.r := hS₁.1
    exact S.chain.endFiltration_antitone (by omega) (sub_mem_of_equivalent hEq.symm)
  have ht : T₁.b - T.b ∈ S.chain.endFiltration (-S₁.r) := by
    rw [hr, hP]
    exact hT₁.2.2
  have hdiff : T₁.b - S₁.b ∈ S.chain.endFiltration (-S₁.r) := by
    rw [show T₁.b - S₁.b = (T₁.b - T.b) + (T.b - S.b) - (S₁.b - S.b) by abel]
    exact sub_mem (add_mem ht hδ) hS₁.2.2
  have heq (U : Str) {a : ℤ} (ha : a < U.n) (he : a = U.r) : atDepth U a ha = U := by
    subst a
    exact atDepth_self U
  have hlt : S₁.r < T₁.n := hr.symm ▸ T₁.r_lt_n
  have he := atDepth_equivalent (S := S₁) (T := T₁) S₁.r_lt_n hlt ho hdiff
  rwa [atDepth_self, heq T₁ hlt hr] at he

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem head_depth_of_no_steps {S : Str} {f : Fin (0 + 1) → Str}
    (hf : S.IsDefiningSequence f) (hb : (f 0).b = S.b) {m : ℕ} (hm : (m : ℤ) < S.n) :
    ((m : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b := by
  rcases choice_terminal hf hb with hc | hc
  · exact hc ▸ WithTop.coe_lt_coe.mpr hm
  · simp [hc]

private theorem terminal_not_step {S T : Str} {f : Fin (0 + 1) → Str} {t : ℕ}
    {g : Fin (t + 1 + 1) → Str} (hf : S.IsDefiningSequence f) (hg : T.IsDefiningSequence g)
    (hb : (f 0).b = S.b) (hc : (g 0).b = T.b) (hEq : S.Equivalent T)
    (hS : S.IsSimple) (hT : T.IsSimple) : False := by
  have h := simpleDepth_eq hEq hS hT
  have hs := choice_step hg hc
  have ht := (stepStratum g hg).r_lt_n
  have hn := n_eq_of_equivalent hEq ⟨hS.1.2, hT.1.2⟩
  rw [hs.2.1] at h
  rcases choice_terminal hf hb with hc' | hc' <;> rw [hc'] at h
  · have hr := WithTop.coe_injective h
    change (stepStratum g hg).r < T.n at ht
    omega
  · exact WithTop.top_ne_coe h

set_option maxHeartbeats 1200000 in
private theorem twist_mem (ψ : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψ)
    (hL : SimpleStratumLatticePropertiesStatement.{uF,uV}) (hLocal : TwistPreservesLocalConditions (V := V) ψ) :
    ∀ (s : ℕ) (S T : Str) (f : Fin (s + 1) → Str) (hf : S.IsDefiningSequence f) (hb : (f 0).b = S.b)
      (q' : T.DefiningSequenceChoice) (m : ℕ), S.IsSimple → T.IsSimple → 0 ≤ S.r → S.Equivalent T →
      S.r / 2 ≤ (m : ℤ) → (m : ℤ) < S.n →
      let q := choiceFromTerms S s f hf hb
      ∀ θ ∈ characterSet ψ S q m, ∀ θ' : characterDomain T q' m →* ℂˣ,
        characterAgreesOn (characterDomain T q' m) θ' θ
          (elementCharacter (traceCharacter ψ) (T.b - S.b)) → θ' ∈ characterSet ψ T q' m := by
  intro s
  induction s with
  | zero =>
    intro S T f hf hb q' m hS hT hS₀ hEq hm hmn
    rcases q' with ⟨t, g, hg, hc⟩
    cases t with
    | succ t => exact (terminal_not_step hf hg hb hc hEq hS hT).elim
    | zero =>
      let q := choiceFromTerms S 0 f hf hb
      let q' := choiceFromTerms T 0 g hg hc
      have hl := hLocal S T hS hT hS₀ hEq q q' m hm hmn (head_depth_of_no_steps hf hb hmn)
      have hn := n_eq_of_equivalent hEq ⟨hS.1.2, hT.1.2⟩
      have ho := order_eq_of_equivalent hEq
      have hunit : S.chain.unitFiltration (simpleHCutoff S.n).toNat =
          T.chain.unitFiltration (simpleHCutoff T.n).toNat := by
        rw [← hn, LatticeChain.unitFiltration_eq_of_order_eq ho]
      have htail : q.tail = [] := List.ofFn_zero
      have htail' : q'.tail = [] := List.ofFn_zero
      change twistMembership ψ S T q.tail q'.tail m
      rw [htail, htail'] at hl ⊢
      intro θ hθ θ' ht
      obtain ⟨hd, _⟩ := hl θ hθ θ' ht
      rw [simpleCharacters, Set.mem_ofPred_eq] at hθ ⊢
      refine ⟨?_, hd⟩
      intro x hx
      obtain ⟨_, hxS, hval⟩ := ht x
      rw [hval, hθ.1 ⟨_, hxS⟩ (hunit ▸ hx), ← elementCharacter_add]
      congr 1
      abel
  | succ s ih =>
    intro S T f hf hb q' m hS hT hS₀ hEq hm hmn
    rcases q' with ⟨t, g, hg, hc⟩
    cases t with
    | zero => exact (terminal_not_step hg hf hc hb hEq.symm hT hS).elim
    | succ t =>
      let S₁ := stepStratum f hf
      let T₁ := stepStratum g hg
      let q₁ := choiceDrop f hf
      let q₁' := choiceDrop g hg
      let q := choiceFromTerms S (s + 1) f hf hb
      let q' := choiceFromTerms T (t + 1) g hg hc
      have h₁Eq := steps_equivalent hf hg hb hc hEq hS hT
      have h₁S := stepStratum_isSimple hf
      have h₁T := stepStratum_isSimple hg
      have h₁r : S₁.r = T₁.r := r_eq_of_equivalent h₁Eq
      have h₁S₀ : 0 ≤ S₁.r := hS₀.trans (choice_step hf hb).1.le
      have h₁crit : (T₁.r : WithTop ℤ) < simpleCriticalDepth S₁.chain S₁.b :=
        h₁r ▸ (simpleCriticalDepth_coe_lt_iff _ _ _).2 h₁S.2
      have hδ₁ := sub_mem_of_equivalent h₁Eq.symm
      have hr := r_eq_of_equivalent hEq
      have hT₀ : 0 ≤ T.r := hr ▸ hS₀
      have hn := n_eq_of_equivalent hEq ⟨hS.1.2, hT.1.2⟩
      have hScrit : finiteCriticalDepth S.chain S.n S.b = S₁.r := by
        rw [finiteCriticalDepth, (choice_step hf hb).2.1, WithTop.untopD_coe]
      have hTcrit : finiteCriticalDepth T.chain T.n T.b = S₁.r := by
        rw [finiteCriticalDepth, (choice_step hg hc).2.1, WithTop.untopD_coe, ← h₁r]
      have htail : q.tail = S₁.b :: q₁.tail := choice_cons_tail hf hb
      have htail' : q'.tail = T₁.b :: q₁'.tail := choice_cons_tail hg hc
      have hSgroup {j : ℕ} (hj : S₁.r / 2 ≤ (j : ℤ)) :
          simpleHGroup S.chain S.n S.b (S₁.b :: q₁.tail) (j + 1) = characterDomain S₁ q₁ j := by
        have he := step_group_eq hL hS hS₀ hf hb hj
        change characterDomain S q j = characterDomain S₁ q₁ j at he
        rw [characterDomain, htail] at he
        exact he
      have hTgroup {j : ℕ} (hj : S₁.r / 2 ≤ (j : ℤ)) :
          simpleHGroup T.chain T.n T.b (T₁.b :: q₁'.tail) (j + 1) = characterDomain T₁ q₁' j := by
        rw [h₁r] at hj
        have he := step_group_eq hL hT hT₀ hg hc hj
        change characterDomain T q' j = characterDomain T₁ q₁' j at he
        rw [characterDomain, htail'] at he
        exact he
      have hnext (j : ℕ) (hj : S₁.r / 2 ≤ (j : ℤ)) (hjn : (j : ℤ) < S₁.n)
          (χ : characterDomain S₁ q₁ j →* ℂˣ) (hχ : χ ∈ characterSet ψ S₁ q₁ j) :
          ∃ χ' ∈ characterSet ψ T₁ q₁' j, characterAgreesOn (characterDomain T₁ q₁' j) χ' χ
            (elementCharacter (traceCharacter ψ) (T₁.b - S₁.b)) := by
        have he := simpleHGroup_eq_at_equivalence hL h₁S h₁S₀ h₁T q₁ q₁'
          (order_eq_of_equivalent h₁Eq) (n_eq_of_equivalent h₁Eq ⟨h₁S.1.2, h₁T.1.2⟩)
          h₁crit (h₁r ▸ hδ₁) (h₁r ▸ hj)
        have hk : 1 ≤ ((j + 1 : ℕ) : ℤ) + (j + 1 : ℕ) - S₁.r := by omega
        obtain ⟨χ', hχ'⟩ := exists_twisted_character ψ hψ S₁.chain hk hδ₁ he
          (simpleHGroup_le_unitFiltration S₁.chain S₁.n S₁.b q₁.tail (j + 1)) χ
        refine ⟨χ', ?_, hχ'⟩
        exact ih S₁ T₁ (fun i => f i.succ) q₁.isDefiningSequence rfl q₁' j
          h₁S h₁T h₁S₀ h₁Eq hj hjn χ hχ χ' hχ'
      have htLocal (h : (m : ℤ) < S₁.r) := hLocal S T hS hT hS₀ hEq q q' m hm hmn
        ((choice_step hf hb).2.1 ▸ WithTop.coe_lt_coe.mpr h)
      change twistMembership ψ S T q.tail q'.tail m
      rw [htail, htail'] at htLocal ⊢
      intro θ hθ θ' hagree
      by_cases hlow : (m : ℤ) < S₁.r
      · obtain ⟨hdet, hnorm⟩ := htLocal hlow θ hθ θ' hagree
        rw [simpleCharacters, hScrit, ite_eq_left hlow, Set.mem_ofPred_eq] at hθ
        rw [simpleCharacters, hTcrit, ite_eq_left hlow, Set.mem_ofPred_eq]
        let j := max m (S₁.r / 2).toNat
        have hj : S₁.r / 2 ≤ (j : ℤ) := by dsimp [j]; omega
        have hjmn : (j : ℤ) < S₁.n := by
          have hrn : S₁.r < S.n := S₁.r_lt_n
          change (j : ℤ) < S.n
          dsimp [j]
          omega
        obtain ⟨χ, hχ, hχv⟩ := hθ.2.2
        obtain ⟨χ', hχ', hχ'v⟩ := hnext j hj hjmn χ hχ
        refine ⟨hdet, hnorm, χ', hχ', ?_⟩
        have hSS := hSgroup hj
        have hTT := hTgroup hj
        intro x
        have hmj : m + 1 ≤ j + 1 := by dsimp [j]; omega
        have hxT : (x : G) ∈ simpleHGroup T.chain T.n T.b (T₁.b :: q₁'.tail) (m + 1) :=
          simpleHGroup_antitone T.chain T.n T.b _ hmj x.property
        have hx₁T : (x : G) ∈ characterDomain T₁ q₁' j := hTT.le x.property
        obtain ⟨_, hxS, hp⟩ := hagree ⟨x, hxT⟩
        obtain ⟨_, hx₁S, hq⟩ := hχ'v ⟨x, hx₁T⟩
        obtain ⟨hyS, hy₁S, ht⟩ := hχv ⟨x, hSS.symm.le hx₁S⟩
        refine ⟨hxT, hx₁T, ?_⟩
        have hcoeff : (S.b - S₁.b) + (T.b - S.b) = (T₁.b - S₁.b) + (T.b - T₁.b) := by abel
        let E (b : A) := elementCharacter (traceCharacter ψ) b (x : G)
        change (θ' ⟨(x : G), hxT⟩ : ℂ) = (θ ⟨(x : G), hxS⟩ : ℂ) * E (T.b - S.b) at hp
        change (χ' ⟨(x : G), hx₁T⟩ : ℂ) = (χ ⟨(x : G), hx₁S⟩ : ℂ) * E (T₁.b - S₁.b) at hq
        change (θ ⟨(x : G), hyS⟩ : ℂ) = (χ ⟨(x : G), hy₁S⟩ : ℂ) * E (S.b - S₁.b) at ht
        change (θ' ⟨(x : G), hxT⟩ : ℂ) = (χ' ⟨(x : G), hx₁T⟩ : ℂ) * E (T.b - T₁.b)
        have hadd (a b : A) : E (a + b) = E a * E b := elementCharacter_add _ _ _ _
        rw [hp, ht, hq, mul_assoc, mul_assoc, ← hadd, ← hadd, hcoeff]
      · rw [simpleCharacters, hScrit, ite_eq_right hlow, Set.mem_ofPred_eq] at hθ
        rw [simpleCharacters, hTcrit, ite_eq_right hlow, Set.mem_ofPred_eq]
        have hj : S₁.r / 2 ≤ (m : ℤ) := by omega
        obtain ⟨χ, hχ, _, hχv⟩ := hθ
        obtain ⟨χ', hχ', hχ'v⟩ := hnext m hj hmn χ hχ
        refine ⟨χ', hχ', hTgroup hj, ?_⟩
        intro x
        have hx₁T : (x : G) ∈ characterDomain T₁ q₁' m := (hTgroup hj).le x.property
        obtain ⟨_, hxS, hp⟩ := hagree x
        obtain ⟨hyS, hy₁S, ht⟩ := hχv ⟨x, hxS⟩
        obtain ⟨_, hx₁S, hq⟩ := hχ'v ⟨x, hx₁T⟩
        have hxU := simpleHGroup_le_unitFiltration S.chain S.n S.b (S₁.b :: q₁.tail) (m + 1) hxS
        have hδ := sub_mem_of_equivalent hEq.symm
        have hlt : S.r < S₁.r := (choice_step hf hb).1
        have hk₁ : 1 ≤ -S.r + ((m + 1 : ℕ) : ℤ) := by omega
        have hk₂ : 1 ≤ -S₁.r + ((m + 1 : ℕ) : ℤ) := by omega
        have hp₁ := elementCharacter_eq_one_of_depth S.chain ψ hψ hδ hk₁ hxU
        have hp₂ := elementCharacter_eq_one_of_depth S.chain ψ hψ hδ₁ hk₂ hxU
        refine ⟨x.property, hx₁T, ?_⟩
        let E (b : A) := elementCharacter (traceCharacter ψ) b (x : G)
        change (θ' x : ℂ) = (θ ⟨(x : G), hxS⟩ : ℂ) * E (T.b - S.b) at hp
        change (θ ⟨(x : G), hyS⟩ : ℂ) = (χ ⟨(x : G), hy₁S⟩ : ℂ) * 1 at ht
        change (χ' ⟨(x : G), hx₁T⟩ : ℂ) = (χ ⟨(x : G), hx₁S⟩ : ℂ) * E (T₁.b - S₁.b) at hq
        change E (T.b - S.b) = 1 at hp₁
        change E (T₁.b - S₁.b) = 1 at hp₂
        change (θ' x : ℂ) = (χ' ⟨(x : G), hx₁T⟩ : ℂ) * 1
        rw [hp, ht, hq, hp₁, hp₂, mul_one]

private theorem equiv_twist (ψ : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψ)
    (hL : SimpleStratumLatticePropertiesStatement.{uF,uV})
    (hLocal : TwistPreservesLocalConditions (V := V) ψ)
    {S T : Str} (hS : S.IsSimple) (hT : T.IsSimple) (hS₀ : 0 ≤ S.r) (hEq : S.Equivalent T)
    (q : S.DefiningSequenceChoice) (q' : T.DefiningSequenceChoice)
    {m : ℕ} (hm : S.r / 2 ≤ (m : ℤ)) (hmn : (m : ℤ) < S.n) :
    characterDomain S q m = characterDomain T q' m ∧
      characterSet ψ T q' m = characterSetTwist (characterDomain T q' m) (characterSet ψ S q m)
        (elementCharacter (traceCharacter ψ) (T.b - S.b)) := by
  have hr := r_eq_of_equivalent hEq
  have hn := n_eq_of_equivalent hEq ⟨hS.1.2, hT.1.2⟩
  have hc : (T.r : WithTop ℤ) < simpleCriticalDepth S.chain S.b :=
    hr ▸ (simpleCriticalDepth_coe_lt_iff _ _ _).2 hS.2
  have hDiff := sub_mem_of_equivalent hEq.symm
  have hH := simpleHGroup_eq_at_equivalence hL hS hS₀ hT q q'
    (order_eq_of_equivalent hEq) hn hc (hr ▸ hDiff) (hr ▸ hm)
  refine ⟨hH, ?_⟩
  ext θ'
  constructor
  · intro hθ'
    have hDT := sub_mem_of_equivalent hEq
    have hk : 1 ≤ ((m + 1 : ℕ) : ℤ) + (m + 1 : ℕ) - T.r := by omega
    obtain ⟨θ, hθ⟩ := exists_twisted_character ψ hψ T.chain hk hDT hH.symm
      (simpleHGroup_le_unitFiltration T.chain T.n T.b q'.tail (m + 1)) θ'
    have hθmem : θ ∈ characterSet ψ S q m :=
      twist_mem ψ hψ hL hLocal q'.steps T S q'.terms q'.isDefiningSequence q'.firstElement q m
        hT hS (hr ▸ hS₀) hEq.symm (hr ▸ hm) (hn ▸ hmn) θ' hθ' θ hθ
    refine ⟨θ, hθmem, ?_⟩
    simpa only [neg_sub] using agreesOn_twist_symm ψ hH.symm hθ
  · rintro ⟨θ, hθ, ha⟩
    exact twist_mem ψ hψ hL hLocal q.steps S T q.terms q.isDefiningSequence q.firstElement q' m
      hS hT hS₀ hEq hm hmn θ hθ θ' ha

private theorem relativeOrderNormalizer_le_normalizer (hL : SimpleStratumLatticePropertiesStatement.{uF,uV})
    (S : Str) (hS : S.IsSimple) (h₀ : 0 ≤ S.r) (q : S.DefiningSequenceChoice) (k : ℕ) :
    relativeOrderNormalizer S.chain S.b ≤
      Subgroup.normalizer (simpleHGroup S.chain S.n S.b q.tail k : Set G) := by
  let S₀ := atDepth S 0 (h₀.trans_lt S.r_lt_n)
  have hcrit : (0 : WithTop ℤ) < simpleCriticalDepth S.chain S.b :=
    lt_of_le_of_lt (WithTop.coe_le_coe.mpr h₀) ((simpleCriticalDepth_coe_lt_iff _ _ _).2 hS.2)
  have hS₀ : S₀.IsSimple := atDepth_isSimple _ hS.1 hcrit
  let q₀ := choiceAtDepth q (h₀.trans_lt S.r_lt_n) hcrit
  have htail : q₀.tail = q.tail := choiceAtDepth_tail _ _ _
  have hconj := ((hL F V S₀ rfl hS₀ q₀).2.2.2.1 k).2
  rw [htail] at hconj
  unfold simpleHGroup
  apply Subgroup.le_normalizer_closure_iff.mpr
  intro g hg x hx
  apply Subgroup.subset_closure
  have hgU : g ∈ Subgroup.normalizer (S.chain.unitFiltration k : Set G) := by
    rw [(normalizer F V S.chain).2.2.1 k]
    exact hg.2
  have hu : g * x * g⁻¹ ∈ S.chain.unitFiltration k := (Subgroup.mem_normalizer_iff.mp hgU x).mp hx.1
  have h1 := one_mem_simpleHLattice S.chain S.n S.b q.tail
  have hsub : (x : A) - 1 ∈ simpleHLayer S.chain S.n S.b q.tail k :=
    ⟨sub_mem hx.2 h1, hx.1.2.2⟩
  obtain ⟨h, _⟩ := hconj g hg ((x : A) - 1)
  have h₁ := h.mpr hsub
  change (g : A) * ((x : A) - 1) * (↑g⁻¹ : A) ∈ simpleHLayer S.chain S.n S.b q.tail k at h₁
  rw [mul_sub, sub_mul, mul_one, Units.mul_inv] at h₁
  have h₂ := add_mem h₁.1 h1
  exact ⟨hu, by simpa only [sub_add_cancel, Units.val_mul] using h₂⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem centralizer_le_formalIntertwining {S T : Str} (hEq : S.Equivalent T) :
    (centralizerUnitGroup T.b : Set G) ⊆ S.formalSelfIntertwining := by
  intro g hg
  have hb : T.b ∈ S.coset := sub_mem_of_equivalent hEq.symm
  refine ⟨T.b, hb, ?_⟩
  have hc : Commute T.b (g : A) := hg
  rw [mul_assoc, hc.eq, ← mul_assoc, Units.inv_mul, one_mul]
  exact hb

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem intertwiningNeighborhood_subset_factor {S : Str} (hS₀ : 0 ≤ S.r)
    (hS : S.IsSimple) (q : S.DefiningSequenceChoice) :
    let z := atDepth S 0 (hS₀.trans_lt S.r_lt_n)
    let hc : (0 : WithTop ℤ) < simpleCriticalDepth S.chain S.b :=
      lt_of_le_of_lt (WithTop.coe_le_coe.mpr hS₀) ((simpleCriticalDepth_coe_lt_iff _ _ _).2 hS.2)
    let q₀ := choiceAtDepth q (hS₀.trans_lt S.r_lt_n) hc
    S.simpleIntertwiningNeighborhood ⊆ simpleCharacterIntertwiningFactor z q₀ S.r.toNat := by
  classical
  dsimp only
  intro g hg
  have hr : (S.r.toNat : ℤ) = S.r := Int.toNat_of_nonneg hS₀
  rcases hg with ⟨hbot, rfl⟩ | ⟨ki, hki, hg⟩
  · have hb : elementAlgebra S.b = ⊥ := by
      by_contra h
      simp [criticalExponent, h] at hbot
    simp [simpleCharacterIntertwiningFactor, atDepth, hb]
  · have hb : elementAlgebra S.b ≠ ⊥ := by
      intro h
      simp [criticalExponent, h] at hki
    have hcrit : finiteCriticalDepth S.chain S.n S.b = -ki := by
      simp only [finiteCriticalDepth, simpleCriticalDepth, hki, WithTop.untopD_coe]
    simp only [simpleCharacterIntertwiningFactor, atDepth, hb, ite_false, Set.mem_ofPred_eq,
      hcrit, hr, neg_neg]
    have hm : -ki - S.r = -(S.r + ki) := by omega
    rw [hm]
    exact Submodule.mem_sup.mpr ⟨_, hg, 0, zero_mem _, add_zero _⟩

private theorem conjugationRatio_of_formallyIntertwining
    (hCov : SimpleCharacterCovarianceStatement.{uF, uV}) (ψ : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψ)
    (S : Str) (hS : S.IsSimple) (hS₀ : 0 ≤ S.r) (q : S.DefiningSequenceChoice)
    {m : ℕ} (hm : S.r / 2 ≤ (m : ℤ)) (hmn : (m : ℤ) < S.n)
    (hmc : ((m : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b)
    {θ : characterDomain S q m →* ℂˣ} (hθ : θ ∈ characterSet ψ S q m)
    {g : G} (hg : g ∈ S.formalSelfIntertwining) : characterConjugationRatio ψ S.b θ g := by
  let z := atDepth S 0 (hS₀.trans_lt S.r_lt_n)
  have hcS := (simpleCriticalDepth_coe_lt_iff S.chain S.b S.r).2 hS.2
  have hc : (0 : WithTop ℤ) < simpleCriticalDepth S.chain S.b :=
    lt_of_le_of_lt (WithTop.coe_le_coe.mpr hS₀) hcS
  let q₀ := choiceAtDepth q (hS₀.trans_lt S.r_lt_n) hc
  have htail : q₀.tail = q.tail := choiceAtDepth_tail _ _ _
  have hz : z.IsSimple := atDepth_isSimple _ hS.1 hc
  let t := S.r.toNat
  have ht : (t : ℤ) = S.r := Int.toNat_of_nonneg hS₀
  have htn : (t : ℤ) < z.n := ht.symm ▸ S.r_lt_n
  have htc : ((t : ℤ) : WithTop ℤ) < simpleCriticalDepth z.chain z.b := ht.symm ▸ hcS
  have htm : t / 2 ≤ m := by omega
  let Y := simpleCharacterIntertwiningFactor z q₀ t
  have hsub : S.simpleIntertwiningNeighborhood ⊆ Y := intertwiningNeighborhood_subset_factor hS₀ hS q
  have hYP : g ∈ Y * (centralizerUnitGroup S.b : Set G) * Y := by
    have := S.chain.finiteDimensional
    rw [simpleIntertwining F V S hS] at hg
    exact Set.mul_subset_mul (Set.mul_subset_mul hsub (fun _ hx => hx)) hsub hg
  let P (u : List A) := ∀ χ ∈ simpleCharacters ψ S.chain S.n S.b u m,
    characterConjugationRatio ψ S.b χ g
  have hformula : P q₀.tail := fun χ hχ =>
    hCov F V ψ hψ z rfl hz q₀ m t hmn htn hmc htc htm χ hχ g hYP
  rw [htail] at hformula
  exact hformula θ hθ

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem twist_intertwined {H K : Subgroup G} (hH : H = K) (ψ : AddChar F ℂ) {b b' : A}
    {θ : H →* ℂˣ} {θ' : K →* ℂˣ} {g : G} (hg : g ∈ centralizerUnitGroup b')
    (hCov : characterConjugationRatio ψ b θ g)
    (hAgree : characterAgreesOn K θ' θ (elementCharacter (traceCharacter ψ) (b' - b))) :
    g ∈ characterSelfIntertwining θ' := by
  subst K
  have hf := (characterAgreesOn_of_le le_rfl le_rfl θ' θ _).1 hAgree
  have hRatio := characterConjugationRatio.of_twist ψ hCov hf
  have hb : b + (b' - b) = b' := by abel
  rw [hb] at hRatio
  have hEq' : (↑g⁻¹ : A) * b' * (g : A) = b' := by
    have hComm : Commute b' (g : A) := hg
    rw [mul_assoc, hComm.eq, ← mul_assoc, Units.inv_mul, one_mul]
  intro x hx
  apply Units.ext
  simpa [hEq', elementCharacter_apply] using hRatio x hx

private theorem preserves_local_conditions (hL : SimpleStratumLatticePropertiesStatement.{uF,uV})
    (hCov : SimpleCharacterCovarianceStatement.{uF, uV})
    (ψ : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψ) : TwistPreservesLocalConditions (V := V) ψ := by
  intro S T hS hT hS₀ hEq q q' m hm hmn hmc θ hθ θ' htw
  have hr := r_eq_of_equivalent hEq
  have hn := n_eq_of_equivalent hEq ⟨hS.1.2, hT.1.2⟩
  have hc := hr ▸ (simpleCriticalDepth_coe_lt_iff _ _ _).2 hS.2
  have hH := simpleHGroup_eq_at_equivalence hL hS hS₀ hT q q'
    (order_eq_of_equivalent hEq) hn hc (hr ▸ sub_mem_of_equivalent hEq.symm) (hr ▸ hm)
  have hI : (centralizerUnitGroup T.b : Set G) ⊆ characterSelfIntertwining θ' := by
    intro g hg
    have h := conjugationRatio_of_formallyIntertwining hCov ψ hψ S hS hS₀ q hm hmn hmc hθ
      (centralizer_le_formalIntertwining hEq hg)
    exact twist_intertwined hH ψ hg h htw
  refine ⟨factorsThroughCentralizerDet_of_intertwined_simpleHGroup intertwinedUnitCharacter
    hT.1 q'.tail θ' hI, fun g hg => ⟨?_, hI hg.1⟩⟩
  exact relativeOrderNormalizer_le_normalizer hL T hT (hr ▸ hS₀) q' (m + 1) hg

end Strata

/-- The induction for choice independence and equivalent-stratum twisting. -/
private theorem simpleCharacterChoice_of_lattice_and_local
    (hL : SimpleStratumLatticePropertiesStatement.{uF,uV})
    (hLocal : ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
      (ψ : AddChar F ℂ), IsBKAdditiveCharacter ψ → TwistPreservesLocalConditions (V := V) ψ) :
    SimpleCharacterChoiceStatement.{uF,uV} := by
  intro F _ _ _ _ V _ _ ψ hψ S hr hS q
  have hS₀ : 0 ≤ S.r := hr ▸ le_rfl
  refine ⟨?_, ?_⟩
  · intro q' m hm
    have h := equiv_twist ψ hψ hL (hLocal F V ψ hψ) hS hS hS₀ (show S.Equivalent S from rfl)
      q q' (m := m) (by rw [hr]; omega) hm
    have hzero : elementCharacter (traceCharacter ψ) (S.b - S.b) = fun _ => 1 := by
      funext g
      simp [elementCharacter_apply]
    rwa [hzero] at h
  · intro T ho hn hT hT₀ hcrit hdiff q' m hm hmn _
    have hℓ : T.r < S.n := hn ▸ T.r_lt_n
    let Sℓ := atDepth S T.r hℓ
    have hSℓ : Sℓ.IsSimple := atDepth_isSimple hℓ hS.1 hcrit
    have he : Sℓ.Equivalent T := by
      have h := atDepth_equivalent hℓ T.r_lt_n ho.symm hdiff
      rwa [atDepth_self] at h
    let qℓ := choiceAtDepth q hℓ hcrit
    have htail : qℓ.tail = q.tail := choiceAtDepth_tail q hℓ hcrit
    have h := equiv_twist ψ hψ hL (hLocal F V ψ hψ) hSℓ hT hT₀ he qℓ q' hm hmn
    unfold characterDomain characterSet at h
    rw [htail] at h
    exact h

/-- The defining-sequence comparison from the lattice, conjugation, and relative determinant formulas. -/
private theorem simpleCharacterChoice_of_covariance (hCov : SimpleCharacterCovarianceStatement.{uF, uV}) :
    SimpleCharacterChoiceStatement.{uF, uV} := by
  apply simpleCharacterChoice_of_lattice_and_local simpleStratumLatticeProperties
  intro F _ _ _ _ V _ _ ψ hψ
  exact preserves_local_conditions simpleStratumLatticeProperties hCov ψ hψ

/-- Independence of defining sequences and the positive twist for equivalent simple strata. -/
theorem simpleCharacterChoice : SimpleCharacterChoiceStatement.{uF, uV} :=
  simpleCharacterChoice_of_covariance simpleCharacterCovariance

end Langlands.BushnellKutzko
