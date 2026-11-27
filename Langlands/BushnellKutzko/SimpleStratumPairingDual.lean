import Langlands.BushnellKutzko.SimpleCharacterRestrictionHigh
import Langlands.BushnellKutzko.CentralizerCharacterDual
import Langlands.BushnellKutzko.SimpleStratumAdjointLayers

/-! # Duality and the adjoint annihilator of a simple stratum -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "O" => 𝒪[F]

/-- The trace character evaluated on the adjoint product `a_b(x) y`. -/
noncomputable def adjointCharacterPair (ψ : AddChar F ℂ) (b x y : A) : ℂ :=
  traceCharacter ψ (adjointMap F b x * y)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem adjointCharacterPair_swap (ψ : AddChar F ℂ) (b x y : A) :
    adjointCharacterPair ψ b x y = (adjointCharacterPair ψ b y x)⁻¹ := by
  rw [adjointCharacterPair, adjointCharacterPair, traceCharacter_apply, traceCharacter_apply,
    trace_adjointMap_mul, LinearMap.trace_mul_comm F x, AddChar.map_neg_eq_inv]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem adjointCharacterPair_add_left (ψ : AddChar F ℂ) (b x z y : A) :
    adjointCharacterPair ψ b (x + z) y = adjointCharacterPair ψ b x y * adjointCharacterPair ψ b z y := by
  simp only [adjointCharacterPair, map_add, add_mul, AddChar.map_add_eq_mul]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem adjointCharacterPair_add_right (ψ : AddChar F ℂ) (b x y z : A) :
    adjointCharacterPair ψ b x (y + z) = adjointCharacterPair ψ b x y * adjointCharacterPair ψ b x z := by
  simp only [adjointCharacterPair, mul_add, AddChar.map_add_eq_mul]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem adjointCharacterPair_add_param (ψ : AddChar F ℂ) (b c x y : A) :
    adjointCharacterPair ψ (b + c) x y = adjointCharacterPair ψ b x y * adjointCharacterPair ψ c x y := by
  have h : adjointMap F (b + c) x = adjointMap F b x + adjointMap F c x := by
    simp only [StratumEquivalence.adjointMap_apply]
    noncomm_ring
  simp only [adjointCharacterPair, h, add_mul, AddChar.map_add_eq_mul]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem traceCharacter_mul_ringCommutator (ψ : AddChar F ℂ) (b x y : A) :
    traceCharacter ψ (b * (x * y - y * x)) = adjointCharacterPair ψ b x y := by
  simp only [adjointCharacterPair, traceCharacter_apply, StratumEquivalence.adjointMap_apply]
  exact congrArg ψ (LinearMap.trace_lie_mul_eq b x y).symm

namespace SimpleStratum

local notation "depth[" s "]" => finiteCriticalDepth (Stratum.chain s) (Stratum.n s) (Stratum.b s)
local notation "jcut[" s "]" => Int.toNat (simpleJCutoff depth[s])
local notation "hcut[" s "]" => Int.toNat (simpleHCutoff depth[s])
local notation "𝔓[" s "]" => LatticeChain.endFiltration (Stratum.chain s)
local notation "𝔥[" s "," q "]" => simpleHLayer (Stratum.chain s) (Stratum.n s) (Stratum.b s)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "𝔧[" s "," q "]" => simpleJLayer (Stratum.chain s) (Stratum.n s) (Stratum.b s)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "ad[" s "]" => adjointMap O (Stratum.b s)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The integer cutoff depth is the level when the defining sequence is terminal. -/
theorem terminal_depth (S : Stratum O F V) (q : S.DefiningSequenceChoice) (hq : q.steps = 0) : depth[S] = S.n := by
  rcases q.terminal_critical hq with hc | hc
  · exact finiteCriticalDepth_eq_of_criticalExponent S.chain S.n S.b S.n hc
  · exact finiteCriticalDepth_of_criticalExponent_bot hc

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The integer cutoff depth is positive on a simple stratum at depth zero. -/
theorem depth_pos (S : Stratum O F V) (hS0 : S.r = 0) (hS : S.IsSimple) : 0 < depth[S] := by
  have hc := hS.2
  rw [hS0] at hc
  exact lt_finiteCriticalDepth_of_criticalExponent_lt (hS0 ▸ S.r_lt_n) hc

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem positive_j (S : Stratum O F V) (hd : 0 < depth[S]) : (jcut[S] : ℤ) = simpleJCutoff depth[S] :=
  Int.toNat_of_nonneg (by unfold simpleJCutoff; omega)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem positive_h (S : Stratum O F V) (hd : 0 < depth[S]) : (hcut[S] : ℤ) = simpleHCutoff depth[S] :=
  Int.toNat_of_nonneg (by unfold simpleHCutoff; omega)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem h_sub_depth (S : Stratum O F V) (hd : 0 < depth[S]) : (hcut[S] : ℤ) - depth[S] = 1 - (jcut[S] : ℤ) := by
  rw [positive_j S hd, positive_h S hd, simpleHCutoff, simpleJCutoff]
  omega

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem tail_nil_iff (S : Stratum O F V) (q : S.DefiningSequenceChoice) : q.tail = [] ↔ q.steps = 0 := by
  rw [← List.length_eq_zero_iff]
  simp [Stratum.DefiningSequenceChoice.tail]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem map_layer_eq_at_cutoff (S : Stratum O F V) (q : S.DefiningSequenceChoice) (hS0 : S.r = 0) (hS : S.IsSimple)
    {k : ℕ} (hk : (k : ℤ) ≤ simpleHCutoff depth[S]) : (𝔥[S,q] k).map ad[S] = (𝔥[S,q] hcut[S]).map ad[S] := by
  have hd := depth_pos S hS0 hS
  change (layer true S.chain S.n S.b q.tail k).map ad[S] = (layer true S.chain S.n S.b q.tail hcut[S]).map ad[S]
  rw [layer_eq_centralizer_sup true S.chain S.n S.b q.tail depth[S] rfl
    (fun ht => terminal_depth S q ((tail_nil_iff S q).mp ht))
    (show 0 ≤ simpleHCutoff depth[S] by unfold simpleHCutoff; omega) hk, Submodule.map_sup]
  apply sup_eq_right.mpr
  rintro _ ⟨x, hx, rfl⟩
  have hz : ad[S] x = 0 := hx.2
  rw [hz]
  exact zero_mem _

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem adjoin_commutator_sub_mem (S : Stratum O F V) {b c x : A} {k r : ℤ}
    (hb : b - c ∈ 𝔓[S] (-r)) (hx : x ∈ 𝔓[S] k) :
    adjointMap O b x - adjointMap O c x ∈ 𝔓[S] (k - r) := by
  rw [StratumEquivalence.adjointMap_apply, StratumEquivalence.adjointMap_apply,
    show b * x - x * b - (c * x - x * c) = (b - c) * x - x * (b - c) by noncomm_ring]
  exact sub_mem (by simpa only [sub_eq_add_neg, add_comm] using S.chain.mul_mem_endFiltration hb hx)
    (by simpa only [sub_eq_add_neg] using S.chain.mul_mem_endFiltration hx hb)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem map_adjoint_sup_eq (S : Stratum O F V) {b c : A} (M : Submodule O A) {k r : ℤ}
    (hM : M ≤ 𝔓[S] k) (hb : b - c ∈ 𝔓[S] (-r)) :
    M.map (adjointMap O b) ⊔ 𝔓[S] (k - r) = M.map (adjointMap O c) ⊔ 𝔓[S] (k - r) := by
  apply le_antisymm
  · refine sup_le ?_ le_sup_right
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.mem_sup.mpr ⟨_, Submodule.mem_map_of_mem hx, _,
      adjoin_commutator_sub_mem S hb (hM hx), by abel⟩
  · refine sup_le ?_ le_sup_right
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.mem_sup.mpr ⟨_, Submodule.mem_map_of_mem hx, _,
      (𝔓[S] (k - r)).neg_mem (adjoin_commutator_sub_mem S hb (hM hx)), by abel⟩

private theorem dual_JLayer_of_cutoff (S : Stratum O F V) (q : S.DefiningSequenceChoice) (hS0 : S.r = 0) (hS : S.IsSimple)
    (ψ : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψ) {k : ℕ} (hk : (k : ℤ) ≤ simpleJCutoff depth[S])
    (hc : traceDualLattice ψ (𝔧[S,q] jcut[S]) = (𝔥[S,q] hcut[S]).map ad[S] ⊔ 𝔓[S] (1 - (jcut[S] : ℤ))) :
    traceDualLattice ψ (𝔧[S,q] k) = (𝔥[S,q] hcut[S]).map ad[S] ⊔ 𝔓[S] (1 - (k : ℤ)) := by
  have hd := depth_pos S hS0 hS
  have hkj : k ≤ jcut[S] := by exact_mod_cast (positive_j S hd) ▸ hk
  have hK : 𝔓[S] (1 - (k : ℤ)) ≤ 𝔓[S] (1 - (jcut[S] : ℤ)) := S.chain.endFiltration_antitone (by omega)
  apply le_antisymm
  · intro z hz
    have hqz := traceDualLattice_antitone ψ (centralizerLattice_le_layer false S.chain S.n S.b q.tail k) hz
    rw [traceDualLattice_centralizerLattice S.chain ψ hψ] at hqz
    obtain ⟨p, hp, v, hv, rfl⟩ := Submodule.mem_sup.mp hqz
    have hzj := traceDualLattice_antitone ψ (layer_antitone false S.chain S.n S.b q.tail hkj) hz
    change p + v ∈ traceDualLattice ψ (𝔧[S,q] jcut[S]) at hzj
    rw [hc] at hzj
    obtain ⟨_, ⟨x, hx, rfl⟩, w, hw, heq⟩ := Submodule.mem_sup.mp hzj
    let u := v - ad[S] x
    have hu : u ∈ (adjointMap F S.b).range := sub_mem hv (LinearMap.mem_range_self _ x)
    have huP : u ∈ 𝔓[S] ((hcut[S] : ℤ) + -depth[S]) := by
      change v - ad[S] x ∈ _
      have he : v - ad[S] x = w - p := by rw [← add_sub_cancel_left p v, ← heq]; abel
      rw [he, show (hcut[S] : ℤ) + -depth[S] = 1 - (jcut[S] : ℤ) by simpa [sub_eq_add_neg] using h_sub_depth S hd]
      exact sub_mem hw (hK hp)
    obtain ⟨y, hy, hya⟩ := S.exists_adjoint_lift hS.1 criticalExponent_le_neg_finiteCriticalDepth
      hcut[S] huP hu
    have hyH := mixedAdjointLattice_le_layer true S hS0 hS q le_rfl (positive_h S hd).ge hy
    have hxy : x + y ∈ 𝔥[S,q] hcut[S] := add_mem hx hyH
    apply Submodule.mem_sup.mpr
    refine ⟨ad[S] (x + y), Submodule.mem_map_of_mem hxy, p, hp, ?_⟩
    have he : ad[S] y = v - ad[S] x := hya
    rw [map_add, he]
    abel
  · refine sup_le ?_ ?_
    · rintro z ⟨x, hx, rfl⟩ u hu
      have hs : 𝔧[S,q] k = centralizerLattice S.chain S.b k ⊔ 𝔧[S,q] jcut[S] :=
        layer_eq_centralizer_sup false S.chain S.n S.b q.tail depth[S] rfl
          (fun ht => terminal_depth S q ((tail_nil_iff S q).mp ht))
          (by change 0 ≤ simpleJCutoff depth[S]; unfold simpleJCutoff; omega) hk
      rw [hs] at hu
      obtain ⟨c, hc', w, hw, rfl⟩ := Submodule.mem_sup.mp hu
      have hzero : adjointMap F S.b c = 0 := hc'.2
      have hc₁ : traceCharacter ψ (ad[S] x * c) = 1 := by
        rw [traceCharacter_apply, show ad[S] x = adjointMap F S.b x from rfl,
          trace_adjointMap_mul, hzero, mul_zero, map_zero, neg_zero, AddChar.map_zero_eq_one]
      have hc₂ : ad[S] x ∈ traceDualLattice ψ (𝔧[S,q] jcut[S]) := by
        rw [hc]
        exact Submodule.mem_sup_left (Submodule.mem_map_of_mem hx)
      change traceCharacter ψ (ad[S] x * (c + w)) = 1
      rw [mul_add, AddChar.map_add_eq_mul, hc₁, hc₂ w hw, one_mul]
    · rw [← traceDualLattice_endFiltration S.chain ψ hψ]
      exact traceDualLattice_antitone ψ inf_le_right

/-- The character dual of `𝔍^k` at or below the `J` cutoff is the sum of
`𝔓^(1-k)` and the adjoint image of `ℌ^(⌊d/2⌋+1)`. -/
theorem traceDualLattice_simpleJLayer (S : Stratum O F V) (q : S.DefiningSequenceChoice) (hS0 : S.r = 0) (hS : S.IsSimple)
    (ψ : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψ) {k : ℕ} (hk : (k : ℤ) ≤ simpleJCutoff depth[S]) :
    traceDualLattice ψ (𝔧[S,q] k) = (𝔥[S,q] hcut[S]).map ad[S] ⊔ 𝔓[S] (1 - (k : ℤ)) := by
  induction hsteps : q.steps using Nat.strong_induction_on generalizing S q k with
  | h count ih =>
    have hd := depth_pos S hS0 hS
    apply dual_JLayer_of_cutoff S q hS0 hS ψ hψ hk
    by_cases hzero : q.steps = 0
    · have htail := (tail_nil_iff S q).mpr hzero
      have hdn := terminal_depth S q hzero
      have hJ : 𝔧[S,q] jcut[S] = 𝔓[S] jcut[S] := by
        have hj : simpleJCutoff S.n = (jcut[S] : ℤ) := by rw [positive_j S hd, hdn]
        change layer false S.chain S.n S.b q.tail jcut[S] = 𝔓[S] jcut[S]
        rw [layer, htail, lattice_nil]
        change (centralizerLattice S.chain S.b 0 ⊔ 𝔓[S] (simpleJCutoff S.n)) ⊓
          𝔓[S] jcut[S] = 𝔓[S] jcut[S]
        rw [hj]
        exact inf_eq_right.mpr le_sup_right
      rw [hJ, traceDualLattice_endFiltration S.chain ψ hψ]
      symm
      apply sup_eq_right.mpr
      rintro _ ⟨x, hx, rfl⟩
      have hval := hS.1.2
      have hb : S.b ∈ 𝔓[S] (-depth[S]) := by
        rw [hdn]
        apply (StratumEquivalence.mem_of_valuation_eq (m := -S.n) ?_).1
        simpa only [WithTop.LinearOrderedAddCommGroup.coe_neg] using hval
      change S.b * x - x * S.b ∈ 𝔓[S] (1 - (jcut[S] : ℤ))
      rw [← h_sub_depth S hd]
      exact sub_mem (by simpa only [sub_eq_add_neg, add_comm] using S.chain.mul_mem_endFiltration hb hx.2)
        (by simpa only [sub_eq_add_neg] using S.chain.mul_mem_endFiltration hx.2 hb)
    · obtain ⟨T, q', r, hchain, hn, hT0, hT, hrp, hrn, hcrit, hnext, hdiff, htail, hshort⟩ :=
        q.exists_suffix hS0 (Nat.pos_of_ne_zero hzero)
      have hdr := finiteCriticalDepth_eq_of_criticalExponent S.chain S.n S.b r hcrit
      have hdt : depth[S] < finiteCriticalDepth T.chain T.n T.b := by
        rw [hchain, hn, hdr]
        exact lt_finiteCriticalDepth_of_criticalExponent_lt hrn hnext
      have hkJ : (jcut[S] : ℤ) ≤ simpleJCutoff (finiteCriticalDepth T.chain T.n T.b) := by
        rw [positive_j S hd]
        unfold simpleJCutoff
        omega
      have hkH : (hcut[S] : ℤ) ≤ simpleHCutoff (finiteCriticalDepth T.chain T.n T.b) := by
        rw [positive_h S hd]
        unfold simpleHCutoff
        omega
      have hJcut : layerCutoff false r = (jcut[S] : ℤ) := by
        change simpleJCutoff r = (jcut[S] : ℤ)
        rw [positive_j S hd, hdr]
      have hHcut : layerCutoff true r = (hcut[S] : ℤ) := by
        change simpleHCutoff r = (hcut[S] : ℤ)
        rw [positive_h S hd, hdr]
      have hJ := layer_eq_suffix false hT0 hT q q' hchain hn hrp hrn hcrit hnext hdiff htail
        (k := jcut[S]) hJcut.le
      have hH := layer_eq_suffix true hT0 hT q q' hchain hn hrp hrn hcrit hnext hdiff htail
        (k := hcut[S]) hHcut.le
      have hd₁ := ih q'.steps (hsteps ▸ hshort) T q' hT0 hT hkJ rfl
      rw [← map_layer_eq_at_cutoff T q' hT0 hT hkH] at hd₁
      change simpleJLayer S.chain S.n S.b q.tail jcut[S] = simpleJLayer T.chain T.n T.b q'.tail jcut[S] at hJ
      change simpleHLayer S.chain S.n S.b q.tail hcut[S] = simpleHLayer T.chain T.n T.b q'.tail hcut[S] at hH
      rw [hJ, hd₁, ← hH, hchain, ← h_sub_depth S hd, hdr]
      simpa only [hdr] using (map_adjoint_sup_eq S (𝔥[S,q] hcut[S]) inf_le_right hdiff).symm

/-- An element of the `J` layer at or below the cutoff lies in the `H`
layer exactly when its adjoint image annihilates the `J` layer. -/
theorem mem_simpleHLayer_iff_adjoint_annihilates (S : Stratum O F V) (q : S.DefiningSequenceChoice) (hS0 : S.r = 0) (hS : S.IsSimple)
    (ψ : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψ) {k : ℕ} (hk : (k : ℤ) ≤ simpleJCutoff depth[S])
    {x : A} (hx : x ∈ 𝔧[S,q] k) :
    x ∈ 𝔥[S,q] k ↔ ad[S] x ∈ traceDualLattice ψ (𝔧[S,q] k) := by
  have hd := depth_pos S hS0 hS
  have hkH : (k : ℤ) ≤ simpleHCutoff depth[S] := by unfold simpleHCutoff simpleJCutoff at *; omega
  have hkh : k ≤ hcut[S] := by rw [← positive_h S hd] at hkH; exact_mod_cast hkH
  have hsplit : 𝔥[S,q] k = centralizerLattice S.chain S.b k ⊔ 𝔥[S,q] hcut[S] :=
    layer_eq_centralizer_sup true S.chain S.n S.b q.tail depth[S] rfl
      (fun ht => terminal_depth S q ((tail_nil_iff S q).mp ht))
      (by change 0 ≤ simpleHCutoff depth[S]; unfold simpleHCutoff; omega) hkH
  rw [traceDualLattice_simpleJLayer S q hS0 hS ψ hψ hk, hsplit]
  constructor
  · intro hxH
    obtain ⟨c, hc, y, hy, rfl⟩ := Submodule.mem_sup.mp hxH
    have he : ad[S] c = 0 := hc.2
    rw [map_add, he, zero_add]
    exact Submodule.mem_sup_left (Submodule.mem_map_of_mem hy)
  · intro ha
    obtain ⟨_, ⟨u, hu, rfl⟩, v, hv, he⟩ := Submodule.mem_sup.mp ha
    have hvR : v ∈ (adjointMap F S.b).range := by
      have eq : adjointMap F S.b (x - u) = v := by
        change ad[S] (x - u) = v
        rw [map_sub, ← he]
        abel
      exact ⟨x - u, eq⟩
    let m := (depth[S] + 1 - (k : ℤ)).toNat
    have hm : (m : ℤ) = depth[S] + 1 - (k : ℤ) := Int.toNat_of_nonneg (by
      unfold simpleJCutoff at hk; omega)
    have hmh : simpleHCutoff depth[S] ≤ (m : ℤ) := by
      rw [hm]; unfold simpleHCutoff simpleJCutoff at *; omega
    have hm' : hcut[S] ≤ m := by rw [← positive_h S hd] at hmh; exact_mod_cast hmh
    have hvP : v ∈ 𝔓[S] ((m : ℤ) + -depth[S]) := by rw [hm, show depth[S] + 1 - (k : ℤ) + -depth[S] = 1 - (k : ℤ) by omega]; exact hv
    obtain ⟨y, hy, hya⟩ := S.exists_adjoint_lift hS.1 criticalExponent_le_neg_finiteCriticalDepth m hvP hvR
    have hyH : y ∈ 𝔥[S,q] hcut[S] := layer_antitone true S.chain S.n S.b q.tail hm'
      (mixedAdjointLattice_le_layer true S hS0 hS q le_rfl hmh hy)
    have huY : u + y ∈ 𝔥[S,q] hcut[S] := add_mem hu hyH
    have hsmall : u + y ∈ 𝔓[S] k := S.chain.endFiltration_antitone (by exact_mod_cast hkh) huY.2
    have hc : x - (u + y) ∈ centralizerLattice S.chain S.b k := by
      refine ⟨sub_mem hx.2 hsmall, ?_⟩
      have hya' : ad[S] y = v := hya
      change ad[S] (x - (u + y)) = 0
      rw [map_sub, map_add, hya', he, sub_self]
    exact Submodule.mem_sup.mpr ⟨_, hc, _, huY, sub_add_cancel _ _⟩

/-- A perturbation at depth `−r` contributes trivially to the adjoint
character product when the two test depths sum to more than `r`. -/
theorem adjointCharacterPair_eq_of_approximation (S : Stratum O F V)
    (ψ : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψ) {b c x y : A} {k l r : ℤ}
    (hbc : b - c ∈ 𝔓[S] (-r)) (hx : x ∈ 𝔓[S] k) (hy : y ∈ 𝔓[S] l) (hdepth : r < k + l) :
    adjointCharacterPair ψ b x y = adjointCharacterPair ψ c x y := by
  have had : (adjointMap O b x - adjointMap O c x) * y ∈ 𝔓[S] 1 :=
    S.chain.endFiltration_antitone (by omega)
      (S.chain.mul_mem_endFiltration (adjoin_commutator_sub_mem S hbc hx) hy)
  have htr := traceCharacter_eq_one_of_mem S.chain ψ hψ had
  change traceCharacter ψ (adjointMap O b x * y) = traceCharacter ψ (adjointMap O c x * y)
  conv_lhs =>
    rw [show adjointMap O b x * y = (adjointMap O b x - adjointMap O c x) * y +
      adjointMap O c x * y by noncomm_ring]
  rw [AddChar.map_add_eq_mul, htr, one_mul]

/-- The additive adjoint-character test detects the `H` layer at every level. -/
theorem mem_simpleHLayer_iff_adjointCharacterPair (S : Stratum O F V) (q : S.DefiningSequenceChoice)
    (hS0 : S.r = 0) (hS : S.IsSimple) (ψ : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψ)
    {k : ℕ} {x : A} (hx : x ∈ 𝔧[S,q] k) :
    x ∈ 𝔥[S,q] k ↔ ∀ y ∈ 𝔧[S,q] k, adjointCharacterPair ψ S.b x y = 1 := by
  induction hsteps : q.steps using Nat.strong_induction_on generalizing S q with
  | h count ih =>
    by_cases hk : (k : ℤ) ≤ simpleJCutoff depth[S]
    · exact mem_simpleHLayer_iff_adjoint_annihilates S q hS0 hS ψ hψ hk hx
    by_cases hzero : q.steps = 0
    · have htail := (tail_nil_iff S q).mpr hzero
      have hdn := terminal_depth S q hzero
      have hH : 𝔓[S] k ≤ 𝔥[S,q] k := by
        change 𝔓[S] k ≤ layer true S.chain S.n S.b q.tail k
        rw [layer, htail, lattice_nil]
        refine le_inf (le_sup_of_le_right (S.chain.endFiltration_antitone ?_)) le_rfl
        change simpleHCutoff S.n ≤ (k : ℤ)
        rw [hdn, simpleJCutoff] at hk
        unfold simpleHCutoff
        omega
      have hb : S.b ∈ 𝔓[S] (-S.n) := by
        apply (StratumEquivalence.mem_of_valuation_eq (m := -S.n) ?_).1
        simpa only [WithTop.LinearOrderedAddCommGroup.coe_neg] using hS.1.2
      refine ⟨fun _ y hy => ?_, fun _ => hH hx.2⟩
      have hgt : S.n < (k : ℤ) + (k : ℤ) := by
        rw [hdn, simpleJCutoff] at hk
        omega
      have he := adjointCharacterPair_eq_of_approximation S ψ hψ
        (show S.b - 0 ∈ 𝔓[S] (-S.n) by simpa only [sub_zero] using hb) hx.2 hy.2 hgt
      rw [he]
      simp [adjointCharacterPair, StratumEquivalence.adjointMap_apply]
    · obtain ⟨T, q', r, hchain, hn, hT0, hT, hrp, hrn, hcrit, hnext, hdiff, htail, hshort⟩ :=
        q.exists_suffix hS0 (Nat.pos_of_ne_zero hzero)
      have hdr := finiteCriticalDepth_eq_of_criticalExponent S.chain S.n S.b r hcrit
      rw [hdr] at hk
      have hJ : 𝔧[S,q] k = 𝔧[T,q'] k := layer_eq_suffix false hT0 hT q q' hchain hn hrp hrn
        hcrit hnext hdiff htail (show simpleJCutoff r ≤ (k : ℤ) from (lt_of_not_ge hk).le)
      have hH : 𝔥[S,q] k = 𝔥[T,q'] k := layer_eq_suffix true hT0 hT q q' hchain hn hrp hrn
        hcrit hnext hdiff htail (by change simpleHCutoff r ≤ (k : ℤ); unfold simpleHCutoff simpleJCutoff at *; omega)
      have hgt : r < (k : ℤ) + (k : ℤ) := by unfold simpleJCutoff at hk; omega
      have he (y : A) (hy : y ∈ 𝔧[S,q] k) :
          adjointCharacterPair ψ S.b x y = adjointCharacterPair ψ T.b x y :=
        adjointCharacterPair_eq_of_approximation S ψ hψ hdiff hx.2 hy.2 hgt
      rw [hH]
      refine (ih q'.steps (hsteps ▸ hshort) T q' hT0 hT (hJ ▸ hx) rfl).trans ?_
      constructor
      · intro h y hy
        rw [he y hy]
        exact h y (hJ ▸ hy)
      · intro h y hy
        have hy' : y ∈ 𝔧[S,q] k := hJ.symm ▸ hy
        rw [← he y hy']
        exact h y hy'

end SimpleStratum

end Langlands.BushnellKutzko
