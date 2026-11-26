import Langlands.BushnellKutzko.SimpleStratumLatticeFiltration
import Mathlib.Data.List.OfFn

/-! # Adjoint bimodules and products of simple-stratum lattices -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko.SimpleStratumLattice

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  (L : LatticeChain 𝒪[F] F V)

local notation "A" => Module.End F V
local notation "P" => L.endFiltration
local notation "Q" => centralizerLattice L
local notation "M" => mixedAdjointLattice L
local notation "N" => adjointLattice L
local notation "crit" => criticalExponent L

/-- The information from a defining sequence used by the lattice recursion. Each
nonterminal step has positive finite critical depth and ends at a simple approximation. -/
inductive Sequence (n : ℤ) : A → List A → Prop
  | terminal {b} (hb : Parameter L n b) (hcrit : crit b = ((-n : ℤ) : WithBot ℤ) ∨ crit b = ⊥) :
      Sequence n b []
  | step {b c tail} {r : ℤ} (hb : Parameter L n b) (hr : 0 < r) (hrn : r < n)
      (hcrit : crit b = ((-r : ℤ) : WithBot ℤ)) (hc : crit c < ((-r : ℤ) : WithBot ℤ))
      (hsub : c - b ∈ P (-r)) (next : Sequence n c tail) : Sequence n b (c :: tail)

variable {L} {n : ℤ}

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The parameter at the head of a sequence. -/
theorem Sequence.parameter {b : A} {tail : List A} (h : Sequence L n b tail) : Parameter L n b :=
  match h with
  | .terminal hb _ => hb
  | .step hb _ _ _ _ _ _ => hb

variable (L)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem sequence_of_family (n : ℤ) (s : ℕ) (q : Fin (s + 1) → Stratum 𝒪[F] F V)
    (hP : ∀ i, Parameter L n (q i).b) (hlt : crit (q 0).b < (0 : WithBot ℤ))
    (hdepth : ∀ i, crit (q i).b < ((-(q i).r : ℤ) : WithBot ℤ))
    (hn : ∀ i, (q i).r < n)
    (hstep : ∀ i : Fin s, crit (q i.castSucc).b = ((-(q i.succ).r : ℤ) : WithBot ℤ) ∧
      (q i.succ).b - (q i.castSucc).b ∈ P (-(q i.succ).r))
    (hterm : crit (q (Fin.last s)).b = ((-n : ℤ) : WithBot ℤ) ∨ crit (q (Fin.last s)).b = ⊥) :
    Sequence L n (q 0).b (List.ofFn fun i : Fin s => (q i.succ).b) := by
  induction s with
  | zero =>
    simpa only [List.ofFn_zero, Fin.last_zero] using Sequence.terminal (hP 0) hterm
  | succ s ih =>
    rw [List.ofFn_succ]
    have heq : crit (q 0).b = ((-(q (0 : Fin (s + 1)).succ).r : ℤ) : WithBot ℤ) :=
      (hstep 0).1
    have hr : 0 < (q (0 : Fin (s + 1)).succ).r := by
      rw [heq, ← WithBot.coe_zero, WithBot.coe_lt_coe] at hlt
      omega
    apply Sequence.step (hP 0) hr (hn _) heq (hdepth _) (hstep 0).2
    refine ih (fun i => q i.succ) (fun i => hP i.succ) ?_ (fun i => hdepth i.succ)
      (fun i => hn i.succ) (fun i => ?_) ?_
    · exact (hdepth _).trans (WithBot.coe_lt_coe.mpr (by omega : -(q (0 : Fin (s + 1)).succ).r < 0))
    · convert hstep i.succ using 1 <;> rfl
    · exact hterm

include L in
/-- A full defining-sequence choice gives a sequence for the lattices on any chain
with the same order, provided the head has positive critical depth. -/
theorem sequence_of_choice {S : Stratum 𝒪[F] F V} (q : S.DefiningSequenceChoice)
    (hL : S.chain.order = L.order) (hlt : crit S.b < (0 : WithBot ℤ)) :
    Sequence L S.n S.b q.tail := by
  rcases q.isDefiningSequence with ⟨_, hterms, _, _, _, hstep, hterm, _⟩
  have hP := StratumEquivalence.endFiltration_eq_of_eq
    (show S.chain.endFiltration 0 = P 0 from congrArg Subalgebra.toSubmodule hL)
  rw [← q.firstElement] at hlt ⊢
  refine sequence_of_family L S.n q.steps q.terms ?_ hlt ?_ ?_ ?_ ?_
  · intro i
    obtain ⟨ho, hn, hs⟩ := hterms i
    exact hn ▸ parameter_of_pure L hs.1 (ho.trans hL)
  · intro i
    have h := (hterms i).2.2.2
    have hi := StratumEquivalence.endFiltration_eq_of_eq
      (show (q.terms i).chain.endFiltration 0 = P 0 from
        congrArg Subalgebra.toSubmodule ((hterms i).1.trans hL))
    rwa [StratumEquivalence.criticalExponent_congr hi] at h
  · intro i
    simpa only [(hterms i).2.1] using (q.terms i).r_lt_n
  · intro i
    simpa only [StratumEquivalence.criticalExponent_congr hP, hP] using hstep i
  · simpa only [StratumEquivalence.criticalExponent_congr hP] using hterm

/-- The two parallel lattice constructions of BK93 (3.1.7)–(3.1.8). -/
inductive Kind
  | H
  | J

/-- The cutoff of either construction. -/
def cutoff : Kind → ℤ → ℤ
  | .H => simpleHCutoff
  | .J => simpleJCutoff

/-- Either of the two simple-stratum lattices. -/
def lattice (n : ℤ) : Kind → A → List A → Submodule 𝒪[F] A
  | .H => simpleHLattice L n
  | .J => simpleJLattice L n

/-- A layer of either lattice, written with an integer index for filtration calculations. -/
def layer (n : ℤ) (i : Kind) (b : A) (tail : List A) (k : ℤ) : Submodule 𝒪[F] A :=
  lattice L n i b tail ⊓ P k

local notation "X" => lattice L n
local notation "Xk" => layer L n

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem lattice_nil (i : Kind) (b : A) :
    X i b [] = Q b 0 ⊔ P (cutoff i n) := by
  cases i <;> rfl

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The finite negative critical exponent corresponds to the positive critical depth. -/
theorem simpleCriticalDepth_eq {b : A} {r : ℤ} (hr : crit b = ((-r : ℤ) : WithBot ℤ)) :
    simpleCriticalDepth L b = (r : WithTop ℤ) := by
  simp [simpleCriticalDepth, hr]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem lattice_cons (i : Kind) {b c : A} {tail : List A} {r : ℤ}
    (hr : crit b = ((-r : ℤ) : WithBot ℤ)) :
    X i b (c :: tail) = Q b 0 ⊔ Xk i c tail (cutoff i r) := by
  have hdepth : finiteCriticalDepth L n b = r := by
    simp [finiteCriticalDepth, simpleCriticalDepth_eq L hr]
  cases i <;> simp [lattice, layer, simpleHLattice, simpleJLattice, simpleStratumLattices, hdepth, cutoff]

private theorem cutoff_pos (i : Kind) {r : ℤ} (hr : 0 < r) : 0 < cutoff i r := by
  cases i <;> simp [cutoff, simpleHCutoff, simpleJCutoff] <;> omega

/-- At positive depth each cutoff is at most that depth. -/
theorem cutoff_le (i : Kind) {r : ℤ} (hr : 0 < r) : cutoff i r ≤ r := by
  cases i <;> simp [cutoff, simpleHCutoff, simpleJCutoff] <;> omega

/-- Both cutoffs are monotone and change by at most the change of depth. -/
theorem cutoff_bounds (i : Kind) {t r : ℤ} (h : t ≤ r) :
    cutoff i t ≤ cutoff i r ∧ cutoff i r ≤ cutoff i t + (r - t) := by
  cases i <;> simp [cutoff, simpleHCutoff, simpleJCutoff] <;> omega

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem layer_le (i : Kind) (b : A) (tail : List A) {k l : ℤ} (h : k ≤ l) :
    Xk i b tail l ≤ Xk i b tail k := inf_le_inf_left _ (L.endFiltration_antitone h)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Each lattice contains the integral centralizer. -/
theorem centralizer_le_lattice (i : Kind) (b : A) (tail : List A) : Q b 0 ≤ X i b tail := by
  cases tail <;> cases i <;> exact le_sup_left

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem centralizer_le_layer (i : Kind) (b : A) (tail : List A) {k : ℤ} (hk : 0 ≤ k) :
    Q b k ≤ Xk i b tail k := le_inf
      ((inf_le_inf_right _ (L.endFiltration_antitone hk)).trans (centralizer_le_lattice L i b tail))
      inf_le_left

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem sup_inf_of_le {b : A} {k : ℤ} (hk : 0 ≤ k) {Y : Submodule 𝒪[F] A}
    (hY : Y ≤ P k) : (Q b 0 ⊔ Y) ⊓ P k = Q b k ⊔ Y := by
  have h : Q b 0 ⊓ P k = Q b k := by
    unfold centralizerLattice
    rw [inf_right_comm, inf_eq_right.mpr (L.endFiltration_antitone hk)]
  rw [sup_comm (Q b 0) Y, sup_inf_assoc_of_le (Q b 0) hY, h, sup_comm Y]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem low_layer {i : Kind} {b : A} {tail : List A} {Y : Submodule 𝒪[F] A} {c k : ℤ}
    (h : X i b tail = Q b 0 ⊔ Y) (hY : Y ≤ P c) (hk : 0 ≤ k) (hkc : k ≤ c) :
    Xk i b tail k = Q b k ⊔ Y := by
  rw [layer, h, sup_inf_of_le L hk (hY.trans (L.endFiltration_antitone hkc))]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem high_layer {i : Kind} {b : A} {tail : List A} {Y : Submodule 𝒪[F] A} {c k : ℤ}
    (h : X i b tail = Q b 0 ⊔ Y) (hY : Y ≤ P c) (hc : 0 ≤ c) (hQ : Q b c ≤ Y) (hk : c ≤ k) :
    Xk i b tail k = Y ⊓ P k := by
  have hcut := low_layer L h hY hc (le_refl c)
  rw [sup_eq_right.mpr hQ] at hcut
  change X i b tail ⊓ P k = Y ⊓ P k
  rw [← hcut, layer, inf_assoc, inf_eq_right.mpr (L.endFiltration_antitone hk)]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem whole_filtration_bimodule (b : A) (t k : ℤ) : Bimodule (N b (-t)) (P k) := by
  constructor
  · simpa only [zero_add] using filtration_products L (N b (-t)) (P k) inf_le_left le_rfl
  · simpa only [add_zero] using filtration_products L (P k) (N b (-t)) le_rfl inf_le_left

/-- The ring bounds, adjoint bimodule property and fractional commutation for one of
the simple-stratum lattices. -/
structure Properties (n : ℤ) (i : Kind) (b : A) (tail : List A) : Prop where
  full : P n ≤ lattice L n i b tail
  integral : lattice L n i b tail ≤ P 0
  mul : lattice L n i b tail * lattice L n i b tail ≤ lattice L n i b tail
  adjoint : ∀ t : ℤ, 0 ≤ t → crit b ≤ ((-t : ℤ) : WithBot ℤ) →
    ∀ k : ℤ, cutoff i t ≤ k → Bimodule (N b (-t)) (layer L n i b tail k)
  fractional : ∀ k : ℤ, 0 ≤ k → ∀ m : ℤ,
    Q b m * layer L n i b tail k = layer L n i b tail k * Q b m

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem properties_of_sup {i : Kind} {r : ℤ} {b : A} {tail : List A} (hb : Parameter L n b)
    (hr : 0 < r) (hcrit : crit b = ((-r : ℤ) : WithBot ℤ)) {Y : Submodule 𝒪[F] A}
    (h : X i b tail = Q b 0 ⊔ Y) (hY : Y ≤ P (cutoff i r)) (hfull : P n ≤ Y)
    (hYm : Y * Y ≤ Y) (hYadj : Bimodule (N b (-r)) Y) (hM : M b (cutoff i r) (-r) ≤ Y)
    (hfrac : ∀ k : ℤ, cutoff i r ≤ k → ∀ m : ℤ, Q b m * (Y ⊓ P k) = (Y ⊓ P k) * Q b m) :
    Properties L n i b tail := by
  have hc := (cutoff_pos i hr).le
  have hQ := (centralizerLattice_le_mixedAdjointLattice L b (cutoff i r) (-r)).trans hM
  have hY0 := hY.trans (L.endFiltration_antitone hc)
  refine ⟨by rw [h]; exact hfull.trans le_sup_right,
    by rw [h]; exact sup_le inf_le_left hY0, ?_, ?_, ?_⟩
  · have hbN := StratumEquivalence.centralizerLattice_le_adjointLattice L b (-r)
    rw [h, Submodule.sup_mul, Submodule.mul_sup, Submodule.mul_sup]
    refine sup_le (sup_le ?_ ?_) (sup_le ?_ (hYm.trans le_sup_right))
    · rw [centralizer_mul L b hb.inverse, add_zero]
      exact le_sup_left
    · exact ((mul_le_mul_left hbN Y).trans hYadj.1).trans le_sup_right
    · exact ((mul_le_mul_right hbN Y).trans hYadj.2).trans le_sup_right
  · intro t ht htr k hk
    rw [hcrit, WithBot.coe_le_coe] at htr
    have htr' : t ≤ r := by omega
    have hN := adjointLattice_antitone L b (show -r ≤ -t by omega)
    have hNY : Bimodule (N b (-t)) Y :=
      ⟨(mul_le_mul_left hN Y).trans hYadj.1, (mul_le_mul_right hN Y).trans hYadj.2⟩
    have hk0 : 0 ≤ k := by
      cases i <;> simp [cutoff, simpleHCutoff, simpleJCutoff] at hk <;> omega
    rcases le_or_gt k (cutoff i r) with hkc | hkc
    · rw [low_layer L h hY hk0 hkc]
      have hgap : cutoff i r ≤ k + (r - t) := by
        have := (cutoff_bounds i htr').2
        omega
      have hN' : N b (-t) = Q b 0 ⊔ M b (r - t) (-r) := by
        have heq := mixed_eq_sup L hb hcrit 0 (r - t) (by omega)
        simpa only [zero_add, mixedAdjointLattice_zero, show -r + (r - t) = -t by omega] using heq
      have hMb := (mixed_antitone_left L b (-r) hgap).trans hM
      have hl : N b (-t) * Q b k ≤ Q b k ⊔ Y := by
        rw [hN', Submodule.sup_mul, centralizer_mul L b hb.inverse, zero_add,
          mixed_mul_centralizer L b hb.inverse, add_comm (r - t) k]
        exact sup_le_sup le_rfl hMb
      have hr' : Q b k * N b (-t) ≤ Q b k ⊔ Y := by
        rw [hN', Submodule.mul_sup, centralizer_mul L b hb.inverse, add_zero,
          centralizerLattice_mul_mixedAdjointLattice L b hb.inverse]
        exact sup_le_sup le_rfl hMb
      exact ⟨by rw [Submodule.mul_sup]; exact sup_le hl (hNY.1.trans le_sup_right),
        by rw [Submodule.sup_mul]; exact sup_le hr' (hNY.2.trans le_sup_right)⟩
    · rw [high_layer L h hY hc hQ hkc.le]
      have hp := whole_filtration_bimodule L b t k
      exact ⟨le_inf ((mul_le_mul_right inf_le_left _).trans hNY.1)
        ((mul_le_mul_right inf_le_right _).trans hp.1),
        le_inf ((mul_le_mul_left inf_le_left _).trans hNY.2)
          ((mul_le_mul_left inf_le_right _).trans hp.2)⟩
  · intro k hk m
    rcases le_or_gt k (cutoff i r) with hkc | hkc
    · have hy := hfrac (cutoff i r) le_rfl m
      rw [inf_eq_left.mpr hY] at hy
      rw [low_layer L h hY hk hkc, Submodule.mul_sup, Submodule.sup_mul, hy,
        centralizer_mul L b hb.inverse, centralizer_mul L b hb.inverse, add_comm m k]
    · rw [high_layer L h hY hc hQ hkc.le]
      exact hfrac k hkc.le m

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem mixed_le_layer_of_adjoint {i : Kind} {b : A} {tail : List A}
    (hb : Parameter L n b) {t k : ℤ} (hk : 0 ≤ k)
    (h : Bimodule (N b (-t)) (Xk i b tail k)) : M b k (-t) ≤ Xk i b tail k := by
  have heq := centralizerLattice_mul_mixedAdjointLattice L b hb.inverse k 0 (-t)
  simp only [mixedAdjointLattice_zero, add_zero] at heq
  rw [← heq]
  exact (mul_le_mul_left (centralizer_le_layer L i b tail hk) _).trans h.2

variable {L}

/-- The terminal formulas, including the scalar case, and the critical approximation
step give the adjoint bimodule and fractional multiplication properties. -/
theorem Sequence.properties {b : A} {tail : List A} (hseq : Sequence L n b tail) (hn : 0 < n) (i : Kind) :
    Properties L n i b tail := by
  induction hseq with
  | terminal hb hcrit =>
    rename_i b
    rcases hcrit with hcrit | hcrit
    · have hM := mixed_eq_filtration L hb.mem
      have hc := (cutoff_pos i hn).le
      have hYm : P (cutoff i n) * P (cutoff i n) ≤ P (cutoff i n) :=
        (filtration_products L _ _ le_rfl le_rfl).trans (L.endFiltration_antitone (by omega))
      apply properties_of_sup L hb hn hcrit (lattice_nil L i b) le_rfl
        (L.endFiltration_antitone (cutoff_le i hn)) hYm
        (whole_filtration_bimodule L b n _) (hM _).le
      intro k hk m
      rw [inf_eq_right.mpr (L.endFiltration_antitone hk)]
      have hn₀ := hM k
      rw [← hn₀, centralizerLattice_mul_mixedAdjointLattice L b hb.inverse,
        mixed_mul_centralizer L b hb.inverse, add_comm m k]
    · have hX : lattice L n i b [] = P 0 := by
        rw [lattice_nil, centralizer_eq_filtration L hcrit,
          sup_eq_left.mpr (L.endFiltration_antitone (cutoff_pos i hn).le)]
      have hL (k : ℤ) (hk : 0 ≤ k) : layer L n i b [] k = P k := by
        rw [layer, hX, inf_eq_right.mpr (L.endFiltration_antitone hk)]
      refine ⟨by rw [hX]; exact L.endFiltration_antitone hn.le, hX.le, ?_, ?_, ?_⟩
      · rw [hX, StratumEquivalence.endFiltration_mul_eq, zero_add]
      · intro t ht _ k hk
        have hk' : 0 ≤ k := by
          cases i <;> simp [cutoff, simpleHCutoff, simpleJCutoff] at hk <;> omega
        rw [hL k hk']
        exact whole_filtration_bimodule L b t k
      · intro k hk m
        rw [hL k hk, centralizer_eq_filtration L hcrit, StratumEquivalence.endFiltration_mul_eq,
          StratumEquivalence.endFiltration_mul_eq, add_comm m k]
  | step hb hr hrn hcrit hcrit' hsub next ih =>
    rename_i b c tail r
    have hc := (cutoff_pos i hr).le
    have hcc := ih.adjoint r hr.le hcrit'.le (cutoff i r) le_rfl
    have hN := mixed_eq_of_sub_mem L hsub (le_refl (-r)) 0
    simp only [mixedAdjointLattice_zero] at hN
    have hYadj : Bimodule (N b (-r)) (layer L n i c tail (cutoff i r)) := hN.symm ▸ hcc
    have hYfull : P n ≤ layer L n i c tail (cutoff i r) :=
      le_inf ih.full (L.endFiltration_antitone ((cutoff_le i hr).trans hrn.le))
    have hYmul : layer L n i c tail (cutoff i r) * layer L n i c tail (cutoff i r) ≤
        layer L n i c tail (cutoff i r) := le_inf
      ((mul_le_mul' inf_le_left inf_le_left).trans ih.mul)
      ((filtration_products L _ _ inf_le_right inf_le_right).trans (L.endFiltration_antitone (by omega)))
    have hM : M b (cutoff i r) (-r) ≤ layer L n i c tail (cutoff i r) := by
      rw [mixed_eq_of_sub_mem L hsub (le_refl (-r))]
      exact mixed_le_layer_of_adjoint L next.parameter hc hcc
    apply properties_of_sup L hb hr hcrit (lattice_cons L i hcrit) inf_le_right hYfull hYmul hYadj hM
    intro k hk m
    have hx : layer L n i c tail (cutoff i r) ⊓ P k = layer L n i c tail k := by
      rw [layer, inf_assoc, inf_eq_right.mpr (L.endFiltration_antitone hk)]
      rfl
    rw [hx]
    have hprod := transfer_products L hb next.parameter hsub (ih.adjoint r hr.le hcrit'.le k hk) m
    rw [hprod.1, hprod.2]
    exact ih.fractional k (hc.trans hk) m

/-- In positive degrees at or above the cutoff the layer of a nonterminal parameter
is exactly that of its chosen critical approximation. -/
theorem Sequence.high_eq {b c : A} {tail : List A} {r : ℤ} (hseq : Sequence L n b (c :: tail)) (hn : 0 < n)
    (hcrit : crit b = ((-r : ℤ) : WithBot ℤ)) (i : Kind) {k : ℤ} (hk : cutoff i r ≤ k) :
    layer L n i b (c :: tail) k = layer L n i c tail k := by
  cases hseq with
  | step hb hr hrn hcrit' hcrit'' hsub next =>
    rename_i r'
    have hrr : r = r' := neg_injective (WithBot.coe_injective (hcrit.symm.trans hcrit'))
    subst r'
    have hc := (cutoff_pos i hr).le
    have hadj := (next.properties hn i).adjoint r hr.le hcrit''.le (cutoff i r) le_rfl
    have hM : M b (cutoff i r) (-r) ≤ layer L n i c tail (cutoff i r) := by
      rw [mixed_eq_of_sub_mem L hsub (le_refl (-r))]
      exact mixed_le_layer_of_adjoint L next.parameter hc hadj
    rw [high_layer L (lattice_cons L i hcrit) inf_le_right hc
      ((centralizerLattice_le_mixedAdjointLattice L b _ _).trans hM) hk,
      layer, inf_assoc, inf_eq_right.mpr (L.endFiltration_antitone hk)]
    rfl


variable (L)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The H cutoff is no smaller than the J cutoff at every step. -/
theorem lattice_H_le_J (level : ℤ) (b : A) (tail : List A) :
    lattice L level .H b tail ≤ lattice L level .J b tail := by
  have hcut (r : ℤ) : simpleJCutoff r ≤ simpleHCutoff r := by
    unfold simpleJCutoff simpleHCutoff
    omega
  induction tail generalizing b with
  | nil =>
    simpa only [lattice_nil, cutoff] using sup_le_sup_left (L.endFiltration_antitone (hcut level)) (Q b 0)
  | cons c tail ih =>
    change Q b 0 ⊔ (lattice L level .H c tail ⊓ P (simpleHCutoff (finiteCriticalDepth L level b))) ≤
      Q b 0 ⊔ (lattice L level .J c tail ⊓ P (simpleJCutoff (finiteCriticalDepth L level b)))
    exact sup_le_sup_left (inf_le_inf (ih c) (L.endFiltration_antitone (hcut _))) _

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem cross_products_of_sup {b : A} {tail : List A} {YH YJ : Submodule 𝒪[F] A}
    (hH : X .H b tail = Q b 0 ⊔ YH) (hJ : X .J b tail = Q b 0 ⊔ YJ) (hYJ : YJ ≤ P 1)
    (hQY : Q b 1 * YJ ≤ YH) (hYY : YJ * YJ ≤ YH)
    (hfrac : Q b 1 * Xk .J b tail 1 = Xk .J b tail 1 * Q b 1) :
    Q b 1 * X .J b tail ≤ X .H b tail ∧
      Xk .J b tail 1 * Xk .J b tail 1 ≤ X .H b tail := by
  have hq : Q b 1 ≤ Q b 0 := inf_le_inf_right _ (L.endFiltration_antitone (by omega))
  have h₁ : Q b 1 * X .J b tail ≤ X .H b tail := by
    rw [hH, hJ, Submodule.mul_sup]
    refine sup_le ?_ (hQY.trans le_sup_right)
    have hmul := centralizer_mul_le L b 1 0
    rw [add_zero] at hmul
    exact hmul.trans (hq.trans le_sup_left)
  refine ⟨h₁, ?_⟩
  have h₁' : Q b 1 * Xk .J b tail 1 ≤ X .H b tail :=
    (mul_le_mul_right inf_le_left (Q b 1)).trans h₁
  have hJ₁ : Xk .J b tail 1 = Q b 1 ⊔ YJ := low_layer L hJ hYJ (by omega) le_rfl
  nth_rw 1 [hJ₁]
  rw [Submodule.sup_mul]
  refine sup_le h₁' ?_
  rw [hJ₁, Submodule.mul_sup]
  refine sup_le ?_ (hYY.trans (hH.symm ▸ le_sup_right))
  have hy : YJ ≤ Xk .J b tail 1 := hJ₁.symm ▸ le_sup_right
  rw [hfrac] at h₁'
  exact (mul_le_mul_left hy _).trans h₁'

variable {L}

/-- The two cross-product inclusions before intersecting with the ambient depth. -/
theorem Sequence.cross_products {b : A} {tail : List A} (hseq : Sequence L n b tail)
    (hn : 0 < n) : Q b 1 * X .J b tail ≤ X .H b tail ∧
      Xk .J b tail 1 * Xk .J b tail 1 ≤ X .H b tail := by
  induction hseq with
  | terminal hb hcrit =>
    rename_i b
    refine cross_products_of_sup L (lattice_nil L .H b) (lattice_nil L .J b) ?_ ?_ ?_
      ((Sequence.terminal hb hcrit).properties hn .J |>.fractional 1 (by omega) 1)
    · exact L.endFiltration_antitone (cutoff_pos .J hn)
    · exact (filtration_products L _ _ inf_le_left le_rfl).trans
        (L.endFiltration_antitone (by simp only [cutoff, simpleHCutoff, simpleJCutoff]; omega))
    · exact (filtration_products L _ _ le_rfl le_rfl).trans
        (L.endFiltration_antitone (by simp only [cutoff, simpleHCutoff, simpleJCutoff]; omega))
  | step hb hr hrn hcrit hcrit' hsub next ih =>
    rename_i b c tail r
    have hj := cutoff_pos .J hr
    have hqj : Q b 1 * Xk .J c tail (cutoff .J r) ≤ Xk .H c tail (cutoff .H r) := by
      have ha := (next.properties hn .J).adjoint r hr.le hcrit'.le (cutoff .J r) le_rfl
      apply le_inf
      · rw [(transfer_products L hb next.parameter hsub ha 1).1]
        exact (mul_le_mul_right inf_le_left _).trans ih.1
      · exact (filtration_products L _ _ inf_le_left inf_le_right).trans
          (L.endFiltration_antitone (by simp only [cutoff, simpleHCutoff, simpleJCutoff]; omega))
    have hjj : Xk .J c tail (cutoff .J r) * Xk .J c tail (cutoff .J r) ≤
        Xk .H c tail (cutoff .H r) := le_inf
      ((mul_le_mul' (layer_le L .J c tail hj) (layer_le L .J c tail hj)).trans ih.2)
      ((filtration_products L _ _ inf_le_right inf_le_right).trans
        (L.endFiltration_antitone (by simp only [cutoff, simpleHCutoff, simpleJCutoff]; omega)))
    refine cross_products_of_sup L (lattice_cons L .H hcrit) (lattice_cons L .J hcrit)
      (inf_le_right.trans (L.endFiltration_antitone hj)) hqj hjj ?_
    exact ((Sequence.step hb hr hrn hcrit hcrit' hsub next).properties hn .J).fractional 1 (by omega) 1

variable (L)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The critical exponents of equivalent parameters agree when both are simple at the
comparison depth. -/
theorem criticalExponent_eq_of_equiv {b b' : A} {t : ℤ} (hb : Parameter L n b)
    (hb' : Parameter L n b') (ht : crit b < ((-t : ℤ) : WithBot ℤ))
    (ht' : crit b' < ((-t : ℤ) : WithBot ℤ)) (hsub : b' - b ∈ P (-t)) : crit b = crit b' := by
  have hsub' : b - b' ∈ P (-t) := by simpa only [neg_sub] using neg_mem hsub
  exact (StratumEquivalence.sup_eq_and_criticalExponent_eq L hsub'
    hb.criticalSet hb'.criticalSet ht ht').2

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem layer_eq_of_common_tail {i : Kind} {b b' : A} {tail tail' : List A} {r t k : ℤ}
    (hb : Parameter L n b) (hb' : Parameter L n b') (hr : 0 < r) (ht : t < r)
    (hcrit : crit b = ((-r : ℤ) : WithBot ℤ)) (hcrit' : crit b' = ((-r : ℤ) : WithBot ℤ))
    (hsub : b' - b ∈ P (-t)) {Y : Submodule 𝒪[F] A}
    (hX : X i b tail = Q b 0 ⊔ Y) (hX' : X i b' tail' = Q b' 0 ⊔ Y)
    (hY : Y ≤ P (cutoff i r)) (hM : M b (cutoff i r) (-r) ≤ Y)
    (hk : 0 ≤ k) (hbound : t + cutoff i r - r ≤ k) : Xk i b tail k = Xk i b' tail' k := by
  have hm := mixed_eq_of_sub_mem L hsub (show -r ≤ -t by omega) (cutoff i r)
  have hc := (cutoff_pos i hr).le
  rcases le_or_gt k (cutoff i r) with hkc | hkc
  · rw [low_layer L hX hY hk hkc, low_layer L hX' hY hk hkc]
    let d := cutoff i r - k
    have hd : 0 ≤ d := by dsimp [d]; omega
    have hdepth : -r + d ≤ -t := by dsimp [d]; omega
    have hkm : k + d = cutoff i r := by dsimp [d]; omega
    have heq := mixed_eq_of_sub_mem L hsub hdepth k
    rw [mixed_eq_sup L hb hcrit k d hd, mixed_eq_sup L hb' hcrit' k d hd, hkm, ← hm] at heq
    calc
      Q b k ⊔ Y = (Q b k ⊔ M b (cutoff i r) (-r)) ⊔ Y := by
        rw [sup_assoc, sup_eq_right.mpr hM]
      _ = (Q b' k ⊔ M b (cutoff i r) (-r)) ⊔ Y := by rw [heq]
      _ = Q b' k ⊔ Y := by rw [sup_assoc, sup_eq_right.mpr hM]
  · have hQ := (centralizerLattice_le_mixedAdjointLattice L b (cutoff i r) (-r)).trans hM
    have hQ' := (centralizerLattice_le_mixedAdjointLattice L b' (cutoff i r) (-r)).trans (hm ▸ hM)
    rw [high_layer L hX hY hc hQ hkc.le, high_layer L hX' hY hc hQ' hkc.le]

variable {L}

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem Sequence.nil_of_terminal {b : A} {tail : List A} (hseq : Sequence L n b tail)
    (h : crit b = ((-n : ℤ) : WithBot ℤ) ∨ crit b = ⊥) : tail = [] := by
  cases hseq with
  | terminal => rfl
  | step _ _ hrn hcrit _ _ _ =>
    rcases h with h | h
    · have := WithBot.coe_injective (hcrit.symm.trans h)
      omega
    · rw [h] at hcrit
      simp at hcrit

/-- For two equivalent simple parameters with the same level and order, compare
both recursive lattices at every nonnegative layer meeting the relevant cutoff. -/
theorem Sequence.layer_eq_of_equiv {b b' : A} {tail tail' : List A} (hseq : Sequence L n b tail)
    (hseq' : Sequence L n b' tail') (hn : 0 < n) (i : Kind) {t k : ℤ}
    (ht : crit b < ((-t : ℤ) : WithBot ℤ)) (heq : crit b = crit b')
    (hsub : b' - b ∈ P (-t)) (hk : 0 ≤ k)
    (hbound : ∀ {r : ℤ}, crit b = ((-r : ℤ) : WithBot ℤ) → t + cutoff i r - r ≤ k) :
    Xk i b tail k = Xk i b' tail' k := by
  induction hseq generalizing b' tail' t k with
  | terminal hb hcrit =>
    rename_i b
    have hcrit' := hcrit
    rw [heq] at hcrit'
    have hb' := hseq'.parameter
    have ht' := hseq'.nil_of_terminal hcrit'
    subst tail'
    rcases hcrit with hcrit | hcrit
    · have htn : t < n := by rw [hcrit, WithBot.coe_lt_coe] at ht; omega
      exact layer_eq_of_common_tail (L := L) hb hb' hn htn hcrit (heq.symm.trans hcrit) hsub
        (lattice_nil L i b) (lattice_nil L i b') le_rfl (mixed_eq_filtration L hb.mem _).le hk (hbound hcrit)
    · have hs (x : A) (hx : crit x = ⊥) : X i x [] = P 0 := by
        rw [lattice_nil, centralizer_eq_filtration L hx,
          sup_eq_left.mpr (L.endFiltration_antitone (cutoff_pos i hn).le)]
      rw [layer, layer, hs b hcrit, hs b' (heq.symm.trans hcrit)]
  | step hb hr hrn hcrit hc hsub₀ next ih =>
    rename_i b c tail r
    have htr : t < r := by rw [hcrit, WithBot.coe_lt_coe] at ht; omega
    cases hseq' with
    | terminal hb' hend =>
      rcases hend with hend | hend
      · have := WithBot.coe_injective (hcrit.symm.trans (heq.trans hend))
        omega
      · have := hcrit.symm.trans (heq.trans hend)
        simp at this
    | step hb' hr' hrn' hcrit' hc' hsub₀' next' =>
      rename_i c' tail' r'
      have hrr := neg_injective (WithBot.coe_injective (hcrit.symm.trans (heq.trans hcrit')))
      subst r'
      have hsubc : c' - c ∈ P (-r) := by
        have hsub' := L.endFiltration_antitone (show -r ≤ -t by omega) hsub
        have h := sub_mem (add_mem hsub₀' hsub') hsub₀
        rwa [show c' - b' + (b' - b) - (c - b) = c' - c by abel] at h
      have heqc := criticalExponent_eq_of_equiv L next.parameter next'.parameter hc hc' hsubc
      have hk₀ := (cutoff_pos i hr).le
      have hY : Xk i c tail (cutoff i r) = Xk i c' tail' (cutoff i r) := by
        apply ih next' hc heqc hsubc hk₀
        intro s hs
        have hrs : r ≤ s := by rw [hs, WithBot.coe_lt_coe] at hc; omega
        have := (cutoff_bounds i hrs).2
        omega
      have hadj := (next.properties hn i).adjoint r hr.le hc.le (cutoff i r) le_rfl
      have hM : M b (cutoff i r) (-r) ≤ Xk i c tail (cutoff i r) := by
        rw [mixed_eq_of_sub_mem L hsub₀ (le_refl (-r))]
        exact mixed_le_layer_of_adjoint L next.parameter hk₀ hadj
      exact layer_eq_of_common_tail (L := L) hb hb' hr htr hcrit hcrit' hsub (lattice_cons L i hcrit)
        ((lattice_cons L i hcrit').trans (congrArg (Q b' 0 ⊔ ·) hY.symm)) inf_le_right hM hk (hbound hcrit)

/-- At sufficiently high degrees the comparison holds for any simple approximation
at the critical depth, with any of its defining sequences. -/
theorem Sequence.approximation_eq {b c : A} {tail tail' : List A} (hseq : Sequence L n b tail)
    (hseq' : Sequence L n c tail') (hn : 0 < n) (i : Kind) {r k : ℤ} (hrn : r < n)
    (hcrit : crit b = ((-r : ℤ) : WithBot ℤ)) (hc : crit c < ((-r : ℤ) : WithBot ℤ))
    (hsub : c - b ∈ P (-r)) (hk : cutoff i r ≤ k) : Xk i b tail k = Xk i c tail' k := by
  cases hseq with
  | terminal hb hend =>
    rcases hend with hend | hend
    · have := WithBot.coe_injective (hcrit.symm.trans hend)
      omega
    · rw [hend] at hcrit
      simp at hcrit
  | step hb hr hrn' hcrit' hd hsub' next =>
    rename_i d seq r'
    have hrr := neg_injective (WithBot.coe_injective (hcrit.symm.trans hcrit'))
    subst r'
    have hsubc : c - d ∈ P (-r) := by
      have h := sub_mem hsub hsub'
      rwa [show c - b - (d - b) = c - d by abel] at h
    have heq := criticalExponent_eq_of_equiv L next.parameter hseq'.parameter hd hc hsubc
    rw [Sequence.high_eq (.step hb hr hrn' hcrit' hd hsub' next) hn hcrit i hk]
    apply next.layer_eq_of_equiv hseq' hn i hd heq hsubc ((cutoff_pos i hr).le.trans hk)
    intro s hs
    have hrs : r ≤ s := by rw [hs, WithBot.coe_lt_coe] at hd; omega
    have := (cutoff_bounds i hrs).2
    omega

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- In either recursive lattice the summand above the integral centralizer is
already at positive depth. -/
theorem Sequence.lattice_eq_sup_layer_one {b : A} {tail : List A}
    (hseq : Sequence L n b tail) (hn : 0 < n) (i : Kind) :
    X i b tail = Q b 0 ⊔ Xk i b tail 1 := by
  have split {b : A} {tail : List A} {Y : Submodule 𝒪[F] A}
      (h : X i b tail = Q b 0 ⊔ Y) (hy : Y ≤ P 1) : X i b tail = Q b 0 ⊔ Xk i b tail 1 := by
    have hY : Y ≤ X i b tail := h.symm ▸ le_sup_right
    exact (h.le.trans (sup_le_sup_left (le_inf hY hy) _)).antisymm
      (sup_le (centralizer_le_lattice L i b tail) inf_le_left)
  cases hseq with
  | terminal => exact split (lattice_nil L i _) (L.endFiltration_antitone (cutoff_pos i hn))
  | step _ hr _ hcrit _ _ _ =>
    exact split (lattice_cons L i hcrit) (inf_le_right.trans (L.endFiltration_antitone (cutoff_pos i hr)))

end Langlands.BushnellKutzko.SimpleStratumLattice
