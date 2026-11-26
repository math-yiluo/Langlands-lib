import Langlands.BushnellKutzko.SimpleCharacterTransferDepth
import Langlands.BushnellKutzko.DefiningSequenceSuffix
import Langlands.BushnellKutzko.RefinementElementExactness

/-! # Mixed adjoint bounds for the lattice layers of a simple stratum -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "O" => 𝒪[F]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem simpleCriticalDepth_eq_of_criticalExponent
    {L : LatticeChain O F V} {b : A} {r : ℤ}
    (h : criticalExponent L b = ((-r : ℤ) : WithBot ℤ)) :
    simpleCriticalDepth L b = (r : WithTop ℤ) := by
  rw [simpleCriticalDepth, h]
  change ((-(-r) : ℤ) : WithTop ℤ) = _
  rw [neg_neg]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem finiteCriticalDepth_of_criticalExponent_bot
    {L : LatticeChain O F V} {b : A} {n : ℤ} (h : criticalExponent L b = ⊥) :
    finiteCriticalDepth L n b = n := by
  rw [finiteCriticalDepth, simpleCriticalDepth, h]
  rfl

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem criticalExponent_le_neg_finiteCriticalDepth
    {L : LatticeChain O F V} {b : A} {n : ℤ} :
    criticalExponent L b ≤ ((-finiteCriticalDepth L n b : ℤ) : WithBot ℤ) := by
  cases h : criticalExponent L b using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe k =>
    have h' : criticalExponent L b = ((-(-k) : ℤ) : WithBot ℤ) := by simpa using h
    rw [finiteCriticalDepth_eq_of_criticalExponent _ n _ _ h', neg_neg]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem lt_finiteCriticalDepth_of_criticalExponent_lt
    {L : LatticeChain O F V} {b : A} {n r : ℤ} (hr : r < n)
    (h : criticalExponent L b < ((-r : ℤ) : WithBot ℤ)) : r < finiteCriticalDepth L n b := by
  cases hb : criticalExponent L b using WithBot.recBotCoe with
  | bot => rwa [finiteCriticalDepth_of_criticalExponent_bot hb]
  | coe k =>
    have hb' : criticalExponent L b = ((-(-k) : ℤ) : WithBot ℤ) := by simpa using hb
    rw [finiteCriticalDepth_eq_of_criticalExponent _ n _ _ hb']
    rw [hb] at h
    have := WithBot.coe_lt_coe.mp h
    omega

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem elementAlgebra_eq_bot_of_criticalExponent_bot
    {L : LatticeChain O F V} {b : A} (h : criticalExponent L b = ⊥) :
    elementAlgebra b = ⊥ := by
  by_contra hne
  rw [criticalExponent, ite_eq_right hne] at h
  exact WithBot.coe_ne_bot h

/-- Restricting a global adjoint image to a filtration step gives a preimage at
any depth permitted by the critical exponent. -/
theorem Stratum.exists_adjoint_lift (S : Stratum O F V) (hS : S.IsPure) {k : ℤ}
    (hk : criticalExponent S.chain S.b ≤ (k : WithBot ℤ)) (m : ℤ) {y : A}
    (hy : y ∈ S.chain.endFiltration (m + k)) (hrange : y ∈ (adjointMap F S.b).range) :
    ∃ z ∈ mixedAdjointLattice S.chain S.b m k, adjointMap F S.b z = y := by
  let _ := S.chain.finiteDimensional
  rcases hS with ⟨⟨hField, hnorm⟩, _⟩
  obtain ⟨x, rfl⟩ := hrange
  obtain ⟨c, hc, hx⟩ := exists_commute_sub_mem S.chain S.b hField hnorm hk m x hy
  have ha : adjointMap F S.b (x - c) = adjointMap F S.b x := by
    change adjointMap F S.b c = 0 at hc
    rw [map_sub, hc, sub_zero]
  refine ⟨x - c, (mem_mixedAdjointLattice_iff S.chain S.b).mpr ⟨hx, ?_⟩, ha⟩
  rwa [ha]

/-- A preimage bounded at `k-t` separates into its centralizer part and a
part at depth `k+s-t` when the critical exponent is at most `-s`. -/
theorem Stratum.mixedAdjointLattice_le_sup (S : Stratum O F V) (hS : S.IsPure)
    {k s t : ℤ} (ht : t ≤ s)
    (hs : criticalExponent S.chain S.b ≤ ((-s : ℤ) : WithBot ℤ)) :
    mixedAdjointLattice S.chain S.b k (-t) ≤
      centralizerLattice S.chain S.b k ⊔ mixedAdjointLattice S.chain S.b (k + s - t) (-s) := by
  intro x hx
  obtain ⟨hx, hax⟩ := (mem_mixedAdjointLattice_iff S.chain S.b).mp hx
  have hy : adjointMap F S.b x ∈ S.chain.endFiltration (k + s - t + -s) := by
    rwa [show k + s - t + -s = k + -t by omega]
  obtain ⟨y, hy, he⟩ := S.exists_adjoint_lift hS hs (k + s - t) hy (LinearMap.mem_range_self _ _)
  have hyp := S.chain.endFiltration_antitone (show k ≤ k + s - t by omega) hy.1
  apply Submodule.mem_sup.mpr
  refine ⟨x - y, ⟨sub_mem hx hyp, ?_⟩, y, hy, sub_add_cancel _ _⟩
  change adjointMap F S.b (x - y) = 0
  rw [map_sub, he, sub_self]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The mixed adjoint lattices at the approximation depth agree on a common chain. -/
theorem mixedAdjointLattice_eq_of_sub_mem (L : LatticeChain O F V) {b c : A} {r : ℤ}
    (h : b - c ∈ L.endFiltration (-r)) (k : ℤ) :
    mixedAdjointLattice L b k (-r) = mixedAdjointLattice L c k (-r) := by
  ext x
  rw [mem_mixedAdjointLattice_iff, mem_mixedAdjointLattice_iff]
  apply and_congr_right
  intro hx
  have hbc : adjointMap F b x - adjointMap F c x ∈ L.endFiltration (k + -r) := by
    rw [StratumEquivalence.adjointMap_apply, StratumEquivalence.adjointMap_apply,
      show b * x - x * b - (c * x - x * c) = (b - c) * x - x * (b - c) by noncomm_ring]
    exact sub_mem (by simpa only [add_comm] using L.mul_mem_endFiltration h hx)
      (L.mul_mem_endFiltration hx h)
  constructor
  · intro hb
    have e := sub_mem hb hbc
    rwa [sub_sub_cancel] at e
  · intro hc
    have e := add_mem hbc hc
    rwa [sub_add_cancel] at e

namespace SimpleStratum

/-- Select the `H` cutoff when `isH` is true and the `J` cutoff otherwise. -/
abbrev layerCutoff (isH : Bool) (r : ℤ) : ℤ := if isH then simpleHCutoff r else simpleJCutoff r

/-- Select either of the two underlying lattices of a simple stratum. -/
abbrev lattice (isH : Bool) (L : LatticeChain O F V) (n : ℤ) (b : A) (tail : List A) :
    Submodule O A := if isH then simpleHLattice L n b tail else simpleJLattice L n b tail

/-- Select either of the two filtered lattices of a simple stratum. -/
abbrev layer (isH : Bool) (L : LatticeChain O F V) (n : ℤ) (b : A) (tail : List A) (k : ℕ) :
    Submodule O A := lattice isH L n b tail ⊓ L.endFiltration k

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem lattice_nil (isH : Bool) (L : LatticeChain O F V) (n : ℤ) (b : A) :
    lattice isH L n b [] = centralizerLattice L b 0 ⊔ L.endFiltration (layerCutoff isH n) := by
  cases isH <;> rfl

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem lattice_cons (isH : Bool) (L : LatticeChain O F V) (n : ℤ) (b c : A) (tail : List A) :
    lattice isH L n b (c :: tail) = centralizerLattice L b 0 ⊔
      (lattice isH L n c tail ⊓ L.endFiltration (layerCutoff isH (finiteCriticalDepth L n b))) := by
  cases isH <;> rfl

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem layer_antitone (isH : Bool) (L : LatticeChain O F V) (n : ℤ) (b : A) (tail : List A) :
    Antitone (layer isH L n b tail) :=
  fun _ _ h => inf_le_inf_left _ (L.endFiltration_antitone (by exact_mod_cast h))

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem centralizerLattice_le_layer (isH : Bool) (L : LatticeChain O F V) (n : ℤ)
    (b : A) (tail : List A) (k : ℕ) : centralizerLattice L b k ≤ layer isH L n b tail k := by
  have hcentral : centralizerLattice L b 0 ≤ lattice isH L n b tail := by
    cases tail with
    | nil => rw [lattice_nil]; exact le_sup_left
    | cons c rest => rw [lattice_cons]; exact le_sup_left
  intro x hx
  exact ⟨hcentral ⟨L.endFiltration_antitone (Int.natCast_nonneg k) hx.1, hx.2⟩, hx.1⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem layer_eq_endFiltration_of_scalar (isH : Bool) (L : LatticeChain O F V) (n : ℤ)
    (b : A) (tail : List A) (k : ℕ) (hb : elementAlgebra b = ⊥) :
    layer isH L n b tail k = L.endFiltration k := by
  refine inf_le_right.antisymm ?_
  intro x hx
  have hx0 : x ∈ centralizerLattice L b 0 := by
    rw [StratumEquivalence.centralizerLattice_zero_of_bot L hb]
    exact L.endFiltration_antitone (Int.natCast_nonneg k) hx
  exact centralizerLattice_le_layer isH L n b tail k
    ⟨hx, hx0.2⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem layer_split_aux (L : LatticeChain O F V) (b : A) (M : Submodule O A) (k : ℕ)
    (hM : M ≤ L.endFiltration k) :
    (centralizerLattice L b 0 ⊔ M) ⊓ L.endFiltration k = centralizerLattice L b k ⊔ M := by
  rw [sup_comm, sup_inf_assoc_of_le _ hM, sup_comm]
  congr 1
  ext x
  exact ⟨fun hx => ⟨hx.2, hx.1.2⟩,
    fun hx => ⟨⟨L.endFiltration_antitone (Int.natCast_nonneg k) hx.1, hx.2⟩, hx.1⟩⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Below the cutoff the layer is the sum of the current centralizer step and
its layer at the cutoff. -/
theorem layer_eq_centralizer_sup (isH : Bool) (L : LatticeChain O F V) (n : ℤ) (b : A)
    (tail : List A) (d : ℤ) (hd : finiteCriticalDepth L n b = d)
    (hterm : tail = [] → d = n) (hpos : 0 ≤ layerCutoff isH d) {k : ℕ}
    (hk : (k : ℤ) ≤ layerCutoff isH d) :
    layer isH L n b tail k = centralizerLattice L b k ⊔
      layer isH L n b tail (layerCutoff isH d).toNat := by
  let p := (layerCutoff isH d).toNat
  have hp : (p : ℤ) = layerCutoff isH d := Int.toNat_of_nonneg hpos
  have aux (M : Submodule O A) (hM : M ≤ L.endFiltration (layerCutoff isH d)) :
      (centralizerLattice L b 0 ⊔ M) ⊓ L.endFiltration k = centralizerLattice L b k ⊔
        ((centralizerLattice L b 0 ⊔ M) ⊓ L.endFiltration p) := by
    have hQ : centralizerLattice L b p ≤ centralizerLattice L b k :=
      inf_le_inf_right _ (L.endFiltration_antitone (by omega : (k : ℤ) ≤ p))
    rw [layer_split_aux L b M k (hM.trans (L.endFiltration_antitone hk)),
      layer_split_aux L b M p (by rwa [hp]), ← sup_assoc, sup_eq_left.mpr hQ]
  cases tail with
  | nil =>
    simp only [layer, lattice_nil, ← hterm rfl]
    exact aux _ le_rfl
  | cons c tail =>
    simp only [layer, lattice_cons, hd]
    exact aux _ inf_le_right

/-- On every suffix of a defining sequence, a mixed adjoint preimage whose
first index lies beyond the corresponding cutoff is in the simple-stratum layer. -/
theorem mixedAdjointLattice_le_layer (isH : Bool) (S : Stratum O F V) (hS0 : S.r = 0)
    (hS : S.IsSimple) (q : S.DefiningSequenceChoice) {t : ℤ} {k : ℕ}
    (ht : t ≤ finiteCriticalDepth S.chain S.n S.b) (hk : layerCutoff isH t ≤ (k : ℤ)) :
    mixedAdjointLattice S.chain S.b k (-t) ≤ layer isH S.chain S.n S.b q.tail k := by
  induction hsteps : q.steps using Nat.strong_induction_on generalizing S q t k with
  | h a ih =>
    let d := finiteCriticalDepth S.chain S.n S.b
    let l := ((k : ℤ) + d - t).toNat
    have hl : (l : ℤ) = (k : ℤ) + d - t := Int.toNat_of_nonneg (by omega)
    have hcut : layerCutoff isH d ≤ (l : ℤ) := by
      rw [hl]
      cases isH <;> simp only [layerCutoff, Bool.false_eq_true, ite_false, ite_true, simpleHCutoff,
        simpleJCutoff] at hk ⊢ <;> omega
    have hlarge : (k : ℤ) ≤ l := by omega
    apply (S.mixedAdjointLattice_le_sup hS.1 ht criticalExponent_le_neg_finiteCriticalDepth).trans
    apply sup_le (centralizerLattice_le_layer isH S.chain S.n S.b q.tail k)
    intro x hx
    have hxP : x ∈ S.chain.endFiltration (l : ℤ) := by rw [hl]; exact hx.1
    have hx0 := S.chain.endFiltration_antitone hlarge hxP
    have hxc := S.chain.endFiltration_antitone hcut hxP
    by_cases hzero : q.steps = 0
    · have htail : q.tail = [] := List.length_eq_zero_iff.mp (by simp [Stratum.DefiningSequenceChoice.tail, hzero])
      have hdn : d = S.n := by
        rcases q.terminal_critical hzero with h | h
        · exact finiteCriticalDepth_eq_of_criticalExponent _ _ _ _ h
        · exact finiteCriticalDepth_of_criticalExponent_bot h
      change x ∈ lattice isH S.chain S.n S.b q.tail ⊓ S.chain.endFiltration k
      rw [htail, lattice_nil, ← hdn]
      exact ⟨Submodule.mem_sup_right hxc, hx0⟩
    · obtain ⟨T, q', r, hchain, hn, hT0, hT, _, hrn, hcrit, hnext, hdiff, hq, hshort⟩ :=
        q.exists_suffix hS0 (Nat.pos_of_ne_zero hzero)
      have hdr : d = r := finiteCriticalDepth_eq_of_criticalExponent _ _ _ _ hcrit
      have hdt : d ≤ finiteCriticalDepth T.chain T.n T.b := by
        rw [hchain, hn, hdr]
        exact (lt_finiteCriticalDepth_of_criticalExponent_lt hrn hnext).le
      have hdiff' : S.b - T.b ∈ S.chain.endFiltration (-d) := by rwa [hdr]
      have hlift : x ∈ mixedAdjointLattice T.chain T.b l (-d) := by
        rw [hchain, ← mixedAdjointLattice_eq_of_sub_mem S.chain hdiff' l, hl]
        exact hx
      have hout := ih q'.steps (hsteps ▸ hshort) T hT0 hT q' hdt hcut rfl hlift
      rw [hchain, hn] at hout
      change x ∈ lattice isH S.chain S.n S.b q.tail ⊓ S.chain.endFiltration k
      rw [hq, lattice_cons]
      exact ⟨Submodule.mem_sup_right ⟨hout.1, hxc⟩, hx0⟩

/-- Above the current cutoff, the next term of the defining sequence computes the
same filtered lattice. -/
theorem layer_eq_suffix (isH : Bool) {S T : Stratum O F V} (hT0 : T.r = 0) (hT : T.IsSimple)
    (q : S.DefiningSequenceChoice) (q' : T.DefiningSequenceChoice) {r : ℤ}
    (hchain : T.chain = S.chain) (hn : T.n = S.n) (hrpos : 0 < r) (hr : r < S.n)
    (hcrit : criticalExponent S.chain S.b = ((-r : ℤ) : WithBot ℤ))
    (hnext : criticalExponent S.chain T.b < ((-r : ℤ) : WithBot ℤ))
    (hdiff : S.b - T.b ∈ S.chain.endFiltration (-r)) (htail : q.tail = T.b :: q'.tail)
    {k : ℕ} (hk : layerCutoff isH r ≤ (k : ℤ)) :
    layer isH S.chain S.n S.b q.tail k = layer isH T.chain T.n T.b q'.tail k := by
  let p := (layerCutoff isH r).toNat
  have hp : (p : ℤ) = layerCutoff isH r := by
    apply Int.toNat_of_nonneg
    cases isH <;> simp only [layerCutoff, Bool.false_eq_true, ite_false, ite_true, simpleHCutoff,
      simpleJCutoff] <;> omega
  have hstep : centralizerLattice S.chain S.b p ≤ layer isH T.chain T.n T.b q'.tail p := by
    calc
      _ ≤ mixedAdjointLattice S.chain S.b p (-r) :=
          centralizerLattice_le_mixedAdjointLattice S.chain S.b p _
      _ = mixedAdjointLattice T.chain T.b p (-r) := by
          rw [hchain, mixedAdjointLattice_eq_of_sub_mem S.chain hdiff]
      _ ≤ _ := mixedAdjointLattice_le_layer isH T hT0 hT q'
          (by rw [hchain, hn]; exact (lt_finiteCriticalDepth_of_criticalExponent_lt hr hnext).le)
          hp.ge
  rw [hchain, hn] at hstep ⊢
  simp only [layer, htail, lattice_cons, finiteCriticalDepth_eq_of_criticalExponent _ _ _ _ hcrit]
  refine le_antisymm ?_ ?_
  · rintro x ⟨hx, hxP⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    have haP : a ∈ S.chain.endFiltration p := by
      rw [hp]
      have h := sub_mem (S.chain.endFiltration_antitone hk hxP) hb.2
      rwa [add_sub_cancel_right] at h
    exact ⟨add_mem (hstep ⟨haP, ha.2⟩).1 hb.1, hxP⟩
  · rintro x ⟨hx, hxP⟩
    exact ⟨Submodule.mem_sup_right ⟨hx, S.chain.endFiltration_antitone hk hxP⟩, hxP⟩

end SimpleStratum

end Langlands.BushnellKutzko
