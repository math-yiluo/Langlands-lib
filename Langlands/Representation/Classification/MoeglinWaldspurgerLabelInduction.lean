import Langlands.Representation.Classification.MoeglinWaldspurgerDerivationCombinatorics
import Langlands.Representation.Aubert.LanglandsHeadDuality
import Langlands.Representation.Classification.MoeglinWaldspurgerAubertAssembly

/-!
# The derivative-comparison induction for the MW recursion

Assuming an abstract relation `LD` recording the highest left derivative of irreducible
representations with respect to the cuspidals `ν^{x+c} ρ`, together with five structural
facts about it, every Langlands head of a realized integer multisegment `a` is a weak
Zelevinsky label of the realized MW output `dual a`.
-/

noncomputable section

namespace Langlands.MoeglinWaldspurger.Derivation

open Langlands.MoeglinWaldspurger PadicField.TopologicalData
open Aubert Aubert.SegmentPolynomialSurjectivity Aubert.LanglandsHeadDuality

/-- Shorten an interval at its left end, discarding a one-point interval. -/
def Interval.dropFirst (I : Interval) : Multisegment :=
  if h : I.beginning < I.ending then {⟨I.beginning + 1, I.ending, by omega⟩} else 0

/-- No occurrence ending at `c - 1` precedes an occurrence ending at `c`. -/
def Unblocked (b : Multisegment) (c : ℤ) : Prop :=
  ∀ I ∈ b, I.ending = c → ∀ J ∈ b, J.ending = c - 1 → I.beginning ≤ J.beginning

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  (ρ : T.CuspidalDatum.{max uF uV, uF}) (x : ℝ)

/-- `c` is the class of a Langlands head of `realize ρ x b` in rank `n`. -/
def HeadClass (b : Multisegment) (n : ℕ) (c : Label.{uF, uV} F T n) : Prop :=
  letI := T.topology
  ∃ (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) (hπ : π.IsIrreducible),
    GeneralLinear.irreducibleIsoClass n F.Carrier π hπ = c ∧ (realize ρ x b).IsLanglandsHead π

/-- `c` is a weak Zelevinsky label of `realize ρ x b` in rank `n`. -/
def LabelClass (b : Multisegment) (n : ℕ) (c : Label.{uF, uV} F T n) : Prop :=
  IsLabel.{uF, uV} F T (realize ρ x b) n c

/-- The five facts about the highest left derivative used by the induction. -/
structure DerivativeFacts
    (LD : ℤ → ∀ {n m : ℕ}, Label.{uF, uV} F T n → ℕ → Label.{uF, uV} F T m → Prop) : Prop where
  /-- Equal derivative data determine the class. -/
  unique : ∀ (c : ℤ) {n m : ℕ} (cls cls' : Label.{uF, uV} F T n) (K : ℕ)
    (S : Label.{uF, uV} F T m), LD c cls K S → LD c cls' K S → cls = cls'
  /-- Langlands heads without blocking: if every occurrence ends at `c` or `c - 1`, all
  occurrences ending at `c` are shortened. -/
  unblocked : ∀ (b : Multisegment) (c : ℤ), (∀ I ∈ b, TwoEnd c I) → Unblocked b c →
    ∀ {n m : ℕ} (cls : Label.{uF, uV} F T n) (S : Label.{uF, uV} F T m),
      HeadClass F T ρ x b n cls → HeadClass F T ρ x (leftDerivative b c) m S →
        LD c cls (unmatched b c).card S
  /-- Reduction of a Langlands head to its occurrences ending at `c` and `c - 1`. -/
  inert : ∀ (b : Multisegment) (c : ℤ) (δ : Multisegment), (∀ I ∈ δ, TwoEnd c I) →
    ∀ {n₀ m₀ n m : ℕ} (clsJ : Label.{uF, uV} F T n₀) (SJ : Label.{uF, uV} F T m₀)
      (cls : Label.{uF, uV} F T n) (S : Label.{uF, uV} F T m) (K : ℕ),
      HeadClass F T ρ x (b.filter (TwoEnd c)) n₀ clsJ → HeadClass F T ρ x δ m₀ SJ →
      LD c clsJ K SJ → HeadClass F T ρ x b n cls →
      HeadClass F T ρ x (b.filter (fun I => ¬ TwoEnd c I) + δ) m S → LD c cls K S
  /-- Zelevinsky labels at the greatest point of the support. -/
  zmax : ∀ (β : Multisegment) (y : ℤ), (∀ I ∈ β, I.ending ≤ y) →
    ∀ {n m : ℕ} (cls : Label.{uF, uV} F T n) (S : Label.{uF, uV} F T m),
      LabelClass F T ρ x β n cls →
      LabelClass F T ρ x (β - Multiset.replicate (β.count (point y)) (point y)) m S →
        LD y cls (β.count (point y)) S
  /-- Adding an interval with the greatest ending to a Zelevinsky label. -/
  zsocle : ∀ (I : Interval) (ν ν' : Multisegment), (∀ J ∈ ν, J.ending ≤ I.ending) →
    (∀ J ∈ ν', J.ending ≤ I.ending) →
    ∀ {n₁ m₁ n m : ℕ} (cls₁ : Label.{uF, uV} F T n₁) (S₁ : Label.{uF, uV} F T m₁)
      (cls : Label.{uF, uV} F T n) (S : Label.{uF, uV} F T m) (K : ℕ),
      LabelClass F T ρ x ν n₁ cls₁ → LD I.beginning cls₁ K S₁ → LabelClass F T ρ x ν' m₁ S₁ →
      LabelClass F T ρ x (I ::ₘ ν) n cls → LabelClass F T ρ x (Interval.dropFirst I + ν') m S →
        LD I.beginning cls (K + 1) S

section Classification

variable {F T ρ x}

theorem HeadClass.degree {b : Multisegment} {n : ℕ} {c : Label.{uF, uV} F T n}
    (h : HeadClass F T ρ x b n c) : weight b * ρ.rank = n := by
  obtain ⟨π, -, -, hπ⟩ := h
  rw [← realize_degree]
  exact langlandsHead_degree hπ

theorem LabelClass.degree {b : Multisegment} {n : ℕ} {c : Label.{uF, uV} F T n}
    (h : LabelClass F T ρ x b n c) : weight b * ρ.rank = n := by
  rw [← realize_degree]
  exact IsLabel.degree F T h

variable (F T ρ x)

theorem headClass_exists (b : Multisegment) (n : ℕ) (h : weight b * ρ.rank = n) :
    ∃ c : Label.{uF, uV} F T n, HeadClass F T ρ x b n c := by
  let := T.topology
  rw [← realize_degree ρ x b] at h
  subst h
  obtain ⟨π, hπ⟩ := Classification.multisegmentHeadExistence.{uF, uV} F T (realize ρ x b)
  have hirr := langlandsHead_isIrreducible hπ
  exact ⟨_, π, hirr, rfl, hπ⟩

theorem labelClass_exists (b : Multisegment) (n : ℕ) (h : weight b * ρ.rank = n) :
    ∃ c : Label.{uF, uV} F T n, LabelClass F T ρ x b n c := by
  rw [← realize_degree ρ x b] at h
  exact exists_isLabel_of_degree F T (realize ρ x b) h

theorem headClass_unique {b : Multisegment} {n : ℕ} {c c' : Label.{uF, uV} F T n}
    (h : HeadClass F T ρ x b n c) (h' : HeadClass F T ρ x b n c') : c = c' := by
  let := T.topology
  obtain ⟨π, hπ, rfl, hb⟩ := h
  obtain ⟨π', hπ', rfl, hb'⟩ := h'
  exact (SmoothRep.irreducibleIsoClass_eq_iff hπ hπ').mpr
    ((Classification.multisegmentHeadClassification F T n _ _ π π' hb hb').mp rfl)

end Classification

variable {F T ρ x}
variable {LD : ℤ → ∀ {n m : ℕ}, Label.{uF, uV} F T n → ℕ → Label.{uF, uV} F T m → Prop}

/-- Derivative data of a Langlands head through its occurrences ending at `c` and `c - 1`,
assuming the label correctness for all smaller multisegments. -/
theorem headData_of_twoEnd (hD : DerivativeFacts F T ρ x LD)
    (hTop : TopUnmatchedCompatibility) {W : ℕ}
    (IH : ∀ b : Multisegment, weight b < W → ∀ (n : ℕ) (cls : Label.{uF, uV} F T n),
      HeadClass F T ρ x b n cls → LabelClass F T ρ x (dual b) n cls)
    (b : Multisegment) (c : ℤ) (hJ : weight (b.filter (TwoEnd c)) < W)
    {n m : ℕ} (cls : Label.{uF, uV} F T n) (S : Label.{uF, uV} F T m)
    (hb : HeadClass F T ρ x b n cls) (hS : HeadClass F T ρ x (leftDerivative b c) m S) :
    LD c cls (unmatched b c).card S := by
  have hJtwo : ∀ I ∈ b.filter (TwoEnd c), TwoEnd c I := fun I hI => (Multiset.mem_filter.mp hI).2
  obtain ⟨clsJ, hclsJ⟩ := headClass_exists F T ρ x (b.filter (TwoEnd c)) _ rfl
  have hJlab := IH _ hJ _ clsJ hclsJ
  have hδw : weight (leftDerivative (b.filter (TwoEnd c)) c) < W := by
    have := weight_leftDerivative_add_card (b.filter (TwoEnd c)) c
    omega
  obtain ⟨SJ, hSJ⟩ := headClass_exists F T ρ x (leftDerivative (b.filter (TwoEnd c)) c) _ rfl
  have hδlab := IH _ hδw _ SJ hSJ
  obtain ⟨hcount, hdual⟩ := hTop (b.filter (TwoEnd c)) c hJtwo
  have hJend : ∀ I ∈ dual (b.filter (TwoEnd c)), I.ending ≤ c := by
    apply dual_ending_le
    intro I hI
    rcases hJtwo I hI with h | h <;> omega
  have hz := hD.zmax (dual (b.filter (TwoEnd c))) c hJend clsJ SJ hJlab
    (by rw [hcount, ← hdual]; exact hδlab)
  rw [hcount, unmatched_filter] at hz
  refine hD.inert b c (leftDerivative (b.filter (TwoEnd c)) c)
    (twoEnd_of_mem_leftDerivative hJtwo) clsJ SJ cls S _ hclsJ hSJ hz hb ?_
  rw [← leftDerivative_eq_filter_add]
  exact hS

omit [Fact p.Prime] in
theorem unblocked_of_tail_nil {a : Multisegment} {r : Round} (h : round a = some r)
    (ht : r.tail = []) :
    Unblocked a r.first.ending ∧ Unblocked r.residual r.first.ending := by
  have hchain := round_chain_eq h
  have hpick : pick (a.erase r.first) (r.first.ending - 1) r.first.beginning = none := by
    rw [← chain_eq_nil_iff, hchain, ht]
  have hu : r.untouched = a.erase r.first := by
    have h2 := chain_of_pick_none hpick
    rw [hchain] at h2
    exact (Prod.mk.inj h2).2
  have hnone := (Langlands.MoeglinWaldspurger.Involution.pick_none_iff _ _ _).mp hpick
  have hfirst := Langlands.MoeglinWaldspurger.round_first_mem h
  have hI : ∀ I ∈ a, I.ending = r.first.ending → I.beginning ≤ r.first.beginning := by
    intro I hIa hIe
    rcases (Langlands.MoeglinWaldspurger.Involution.interval_le_iff _ _).mp (round_first_maximal h hIa) with hlt | ⟨_, hb⟩
    · omega
    · exact hb
  have hJ : ∀ J ∈ a.erase r.first, J.ending = r.first.ending - 1 →
      r.first.beginning ≤ J.beginning := by
    intro J hJa hJe
    rcases hnone J hJa with hn | hn
    · exact absurd hJe hn
    · exact hn
  refine ⟨?_, ?_⟩
  · intro I hIa hIe J hJa hJe
    have hJne : J ≠ r.first := by
      rintro rfl
      omega
    exact (hI I hIa hIe).trans (hJ J ((Multiset.mem_erase_of_ne hJne).mpr hJa) hJe)
  · have hres : r.residual = a.erase r.first + r.first.dropLast := by
      simp [Round.residual, Round.selected, Round.selectedList, ht, hu, shorten]
    rw [hres]
    intro I hIa hIe J hJa hJe
    have hIb : I.beginning ≤ r.first.beginning := by
      rcases Multiset.mem_add.mp hIa with hI' | hI'
      · exact hI I (Multiset.mem_of_mem_erase hI') hIe
      · unfold Interval.dropLast at hI'
        split_ifs at hI'
        · rw [Multiset.mem_singleton] at hI'
          subst hI'
          simp at hIe
        · simp at hI'
    have hJb : r.first.beginning ≤ J.beginning := by
      rcases Multiset.mem_add.mp hJa with hJ' | hJ'
      · exact hJ J hJ' hJe
      · unfold Interval.dropLast at hJ'
        split_ifs at hJ'
        · rw [Multiset.mem_singleton] at hJ'
          subst hJ'
          exact le_rfl
        · simp at hJ'
    exact hIb.trans hJb

/-- **Label correctness from the derivative facts.** Every Langlands head of `realize ρ x a`
is a weak Zelevinsky label of `realize ρ x (dual a)`. -/
theorem labelClass_of_headClass (hD : DerivativeFacts F T ρ x LD)
    (hTop : TopUnmatchedCompatibility) (hChain : ChainUnmatchedCompatibility) :
    ∀ (a : Multisegment) (n : ℕ) (cls : Label.{uF, uV} F T n),
      HeadClass F T ρ x a n cls → LabelClass F T ρ x (dual a) n cls := by
  let := T.topology
  have hx := Aubert.binaryProductExactness.{uF, uV} F T
  have hl := Aubert.gradedInductionRingLaws F T hx
  obtain ⟨ψ⟩ := HarmonicAnalysis.padicUnitaryAdditiveCharacterExists F T
  suffices hW : ∀ W (a : Multisegment), weight a = W → ∀ (n : ℕ)
      (cls : Label.{uF, uV} F T n), HeadClass F T ρ x a n cls →
        LabelClass F T ρ x (dual a) n cls from
    fun a => hW _ a rfl
  intro W
  induction W using Nat.strong_induction_on with
  | _ W IHW =>
  have IH : ∀ b : Multisegment, weight b < W → ∀ (n : ℕ) (cls : Label.{uF, uV} F T n),
      HeadClass F T ρ x b n cls → LabelClass F T ρ x (dual b) n cls :=
    fun b hb => IHW _ hb b rfl
  intro a ha n cls hcls
  cases hr : round a with
  | none =>
    have ha0 := (round_none_iff a).mp hr
    subst ha0
    have hn : n = 0 := by simpa using hcls.degree.symm
    subst hn
    obtain ⟨c₀, hc₀⟩ := labelClass_exists F T ρ x (dual 0) 0 (by simp)
    obtain ⟨π, hπ, rfl, hhead⟩ := hcls
    have hP := gradedAdjustedOperator_label F T hx hl ψ (realize ρ x 0) 0 c₀
      (by simpa [LabelClass] using hc₀) π hπ hhead
    have hid : gradedAdjustedOperator F T (basisClass F T 0 c₀) = basisClass F T 0 c₀ := by
      unfold basisClass
      rw [gradedAdjustedOperator_homogeneous, adjustedOperator_rankZero, LinearMap.id_apply]
    rw [hid] at hP
    rw [← basisClass_injective F T hP]
    exact hc₀
  | some r =>
    obtain ⟨hcard, hl1, hl2⟩ := hChain a r hr
    set c := r.emitted.beginning with hc
    have he : r.emitted.ending = r.first.ending := rfl
    have hdualA : dual a = r.emitted ::ₘ dual r.residual := dual_of_round hr
    have hwr : weight r.residual < W := ha ▸ round_weight_lt hr
    -- the residual
    obtain ⟨cls₁, hcls₁⟩ := headClass_exists F T ρ x r.residual _ rfl
    have hlab₁ := IH _ hwr _ cls₁ hcls₁
    have hwd₁ : weight (leftDerivative r.residual c) < W := by
      have := weight_leftDerivative_add_card r.residual c
      omega
    obtain ⟨S₁, hS₁⟩ := headClass_exists F T ρ x (leftDerivative r.residual c) _ rfl
    have hlabS₁ := IH _ hwd₁ _ S₁ hS₁
    -- the input
    have hwd : weight (leftDerivative a c) < W := by
      have := weight_leftDerivative_add_card a c
      omega
    obtain ⟨S, hS⟩ := headClass_exists F T ρ x (leftDerivative a c) _ rfl
    have hlabS := IH _ hwd _ S hS
    -- derivative data of the Langlands heads
    have hLD : LD c cls (unmatched a c).card S ∧
        LD c cls₁ (unmatched r.residual c).card S₁ := by
      by_cases ht : r.tail = []
      · have hce : c = r.first.ending := by
          simp [hc, Round.emitted, ht]
        obtain ⟨hu, -⟩ := unblocked_of_tail_nil hr ht
        rw [← hce] at hu
        have hJ₁ : weight (r.residual.filter (TwoEnd c)) < W :=
          lt_of_le_of_lt (weight_filter_le _ _) hwr
        refine ⟨?_, headData_of_twoEnd hD hTop IH r.residual c hJ₁ cls₁ S₁ hcls₁ hS₁⟩
        by_cases htwo : ∀ I ∈ a, TwoEnd c I
        · exact hD.unblocked a c htwo hu cls S hcls hS
        · push Not at htwo
          obtain ⟨I, hIa, hI⟩ := htwo
          have hJ : weight (a.filter (TwoEnd c)) < W := by
            rw [← ha]
            exact weight_filter_lt a _ hIa hI
          exact headData_of_twoEnd hD hTop IH a c hJ cls S hcls hS
      · have hlt : c < r.first.ending := by
          have : 0 < r.tail.length := List.length_pos_of_ne_nil ht
          simp only [hc, Round.emitted]
          omega
        have hJ : weight (a.filter (TwoEnd c)) < W := by
          rw [← ha]
          refine weight_filter_lt a _ (Langlands.MoeglinWaldspurger.round_first_mem hr) ?_
          unfold TwoEnd
          omega
        have hJ₁ : weight (r.residual.filter (TwoEnd c)) < W :=
          lt_of_le_of_lt (weight_filter_le _ _) hwr
        exact ⟨headData_of_twoEnd hD hTop IH a c hJ cls S hcls hS,
          headData_of_twoEnd hD hTop IH r.residual c hJ₁ cls₁ S₁ hcls₁ hS₁⟩
    -- the label of the output
    obtain ⟨V, hV⟩ := labelClass_exists F T ρ x (dual a) n
      (by rw [weight_dual]; exact hcls.degree)
    have hend₁ : ∀ J ∈ dual r.residual, J.ending ≤ r.emitted.ending :=
      dual_ending_le (round_residual_ending_le hr)
    have hend₁' : ∀ J ∈ dual (leftDerivative r.residual c), J.ending ≤ r.emitted.ending :=
      dual_ending_le (leftDerivative_ending_le (round_residual_ending_le hr) c)
    have hdS : dual (leftDerivative a c) =
        Interval.dropFirst r.emitted + dual (leftDerivative r.residual c) := by
      by_cases ht : r.tail = []
      · have hdrop : Interval.dropFirst r.emitted = 0 := by
          simp [Interval.dropFirst, Round.emitted, ht]
        rw [hdrop, zero_add, hl1 ht]
      · obtain ⟨r', hr', hb', he', hres'⟩ := hl2 ht
        have hlt : r.emitted.beginning < r.emitted.ending := by
          have : 0 < r.tail.length := List.length_pos_of_ne_nil ht
          simp only [Round.emitted]
          omega
        have hdrop : Interval.dropFirst r.emitted = {r'.emitted} := by
          simp only [Interval.dropFirst, hlt, ↓reduceDIte]
          congr 1
          exact Interval.ext hb'.symm he'.symm
        rw [dual_of_round hr', hdrop, hres', Multiset.singleton_add]
    have hVLD := hD.zsocle r.emitted (dual r.residual) (dual (leftDerivative r.residual c))
      hend₁ hend₁' cls₁ S₁ V S _ hlab₁ hLD.2 hlabS₁ (hdualA ▸ hV) (hdS ▸ hlabS)
    rw [← hcard] at hVLD
    have hclsV := hD.unique c cls V _ S hLD.1 hVLD
    rw [hclsV]
    exact hV

/-- The label-correctness target from the derivative facts on every cuspidal line. -/
theorem labelCorrectness_of_derivativeFacts
    (hD : ∀ (ρ : T.CuspidalDatum.{max uF uV, uF}) (x : ℝ), ∃ LD :
      ℤ → ∀ {n m : ℕ}, Label.{uF, uV} F T n → ℕ → Label.{uF, uV} F T m → Prop,
        DerivativeFacts F T ρ x LD)
    (hTop : TopUnmatchedCompatibility) (hChain : ChainUnmatchedCompatibility) :
    LabelCorrectness.{uF, uV} F T := by
  intro ρ x a n π hπ hhead
  obtain ⟨LD, hLD⟩ := hD ρ x
  exact labelClass_of_headClass hLD hTop hChain a n _ ⟨π, hπ, rfl, hhead⟩

end Langlands.MoeglinWaldspurger.Derivation
