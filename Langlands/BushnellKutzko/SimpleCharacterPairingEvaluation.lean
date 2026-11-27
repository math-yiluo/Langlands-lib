import Langlands.BushnellKutzko.SimpleCharacterPairingGroup
import Langlands.BushnellKutzko.SimpleCharacterTransferIntersection
import Langlands.BushnellKutzko.SimpleStratumGroupPropertiesProof
import Langlands.BushnellKutzko.UnitCommutatorTrace

/-! # The equal-depth calculation for evaluated simple-character commutators -/

open ValuativeRel
open scoped commutatorElement Pointwise

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => Aˣ
local notation "O" => 𝒪[F]
local notation "𝔥[" s "," q "]" => simpleHLayer (Stratum.chain s) (Stratum.n s) (Stratum.b s)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "𝔧[" s "," q "]" => simpleJLayer (Stratum.chain s) (Stratum.n s) (Stratum.b s)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "H[" s "," q "]" => simpleHGroup (Stratum.chain s) (Stratum.n s) (Stratum.b s)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "J[" s "," q "]" => simpleJGroup (Stratum.chain s) (Stratum.n s) (Stratum.b s)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "R[" s "]" => relativeUnitFiltration (Stratum.chain s) (Stratum.b s)
local notation "depth[" s "]" => finiteCriticalDepth (Stratum.chain s) (Stratum.n s) (Stratum.b s)
local notation "jcut[" s "]" => Int.toNat (simpleJCutoff depth[s])
local notation "C[" ps "," s "," q "]" => simpleCharacters ps (Stratum.chain s) (Stratum.n s)
  (Stratum.b s) (Stratum.DefiningSequenceChoice.tail q)

/-- Relative-unit character properties used in the equal-depth calculation.
The mixed test uses a relative unit below the cutoff and a unit at the cutoff. -/
def SimpleCharacterRelativeCommutatorLaws : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    (ψ : AddChar F ℂ), IsBKAdditiveCharacter ψ →
    ∀ (S : Stratum 𝒪[F] F V), S.r = 0 → S.IsSimple → ∀ q : S.DefiningSequenceChoice,
    ∀ i : ℕ, (i : ℤ) < depth[S] → ∀ θ ∈ C[ψ,S,q] i,
      (∀ k : ℕ, (R[S] k : Set (Module.End F V)ˣ) ⊆ characterNormalizer θ) ∧
      (∀ x y : (Module.End F V)ˣ, x ∈ centralizerUnitGroup S.b → y ∈ centralizerUnitGroup S.b →
        ∀ h : ⁅x, y⁆ ∈ H[S,q] (i+1), θ ⟨_, h⟩ = 1) ∧
      (∀ k : ℕ, 1 ≤ k → k < jcut[S] → i + 1 ≤ k + k →
        ∀ x y : (Module.End F V)ˣ, x ∈ R[S] k → y ∈ J[S,q] jcut[S] →
          ∀ h : ⁅x, y⁆ ∈ H[S,q] (i+1), θ ⟨_, h⟩ = 1)

namespace SimpleStratum

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem terminal_character_value (ψ : AddChar F ℂ) (L : LatticeChain O F V)
    (n : ℤ) (b : A) (tail : List A) (i : ℕ) (htail : tail = [])
    {θ : simpleHGroup L n b tail (i+1) →* ℂˣ} (hθ : θ ∈ simpleCharacters ψ L n b tail i)
    (x : simpleHGroup L n b tail (i+1))
    (hx : (x : G) ∈ L.unitFiltration (simpleHCutoff n).toNat) :
    (θ x : ℂ) = elementCharacter (traceCharacter ψ) b x := by
  subst tail
  exact hθ.1 x hx

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem approx_character_value (ψ : AddChar F ℂ) (L : LatticeChain O F V)
    (n : ℤ) (b c : A) (tail' tail : List A) (i : ℕ) (htail : tail' = c :: tail)
    (hi : (i : ℤ) < finiteCriticalDepth L n b)
    {θ : simpleHGroup L n b tail' (i+1) →* ℂˣ} (hθ : θ ∈ simpleCharacters ψ L n b tail' i) :
    let s := max i ((finiteCriticalDepth L n b) / 2).toNat
    ∃ η ∈ simpleCharacters ψ L n c tail s,
      characterAgreesOn (simpleHGroup L n b tail' (s+1)) θ η
        (elementCharacter (traceCharacter ψ) (b-c)) := by
  subst tail'
  simp only [simpleCharacters, ite_eq_left hi, Set.mem_ofPred_eq] at hθ
  exact hθ.2.2

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem scalar_centralizes (S : Stratum O F V) (hs : elementAlgebra S.b = ⊥)
    {x : G} (hx : x ∈ S.chain.unitFiltration 0) : x ∈ centralizerUnitGroup S.b := by
  have hxA : (x : A) ∈ centralizerLattice S.chain S.b 0 := by
    rw [StratumEquivalence.centralizerLattice_zero_of_bot S.chain hs]
    exact S.chain.mem_order_iff_mem_endFiltration.mp hx.1
  exact sub_eq_zero.mp hxA.2

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem translated_relative_mem (S : Stratum O F V) {k : ℕ} {g : G} (hg : g ∈ R[S] k) :
    (g : A) - 1 ∈ centralizerLattice S.chain S.b k := by
  refine ⟨hg.2.2.2, ?_⟩
  change adjointMap O S.b ((g : A) - 1) = 0
  rw [map_sub, StratumEquivalence.adjointMap_apply, StratumEquivalence.adjointMap_apply,
    mul_one, one_mul, sub_self, sub_zero, sub_eq_zero]
  exact hg.1

private theorem translated_product_diff_mem (hL : SimpleStratumLatticePropertiesStatement.{uF,uV})
    (S : Stratum O F V) (hS0 : S.r = 0) (hS : S.IsSimple) (q : S.DefiningSequenceChoice)
    {k l : ℕ} (hk : 1 ≤ k) (hkl : k ≤ l) {u w : G} (hu : u ∈ R[S] k) (hw : w ∈ J[S,q] l) :
    ((u * w : G) : A) - 1 - ((w : A) - 1) ∈ 𝔥[S,q] k := by
  have hq := translated_relative_mem S hu
  have hq₁ : (u : A) - 1 ∈ centralizerLattice S.chain S.b 1 :=
    ⟨S.chain.endFiltration_antitone (by exact_mod_cast hk) hq.1, hq.2⟩
  have hwj := (simpleJGroup_mem_iff_of_pos S hS0 hS q (hk.trans hkl)).mp hw
  have hmul := (hL F V S hS0 hS q).2.2.2.2.1.1 l (Submodule.mul_mem_mul hq₁ hwj)
  have hmul' := layer_antitone true S.chain S.n S.b q.tail (show k ≤ l+1 by omega) hmul
  have heq : ((u * w : G) : A) - 1 - ((w : A) - 1) =
      ((u : A) - 1) * ((w : A) - 1) + ((u : A) - 1) := by
    simp only [Units.val_mul]
    noncomm_ring
  rw [heq]
  exact add_mem hmul' (centralizerLattice_le_layer true S.chain S.n S.b q.tail k hq)

private theorem adjointCharacterPair_mul_mul (hL : SimpleStratumLatticePropertiesStatement.{uF,uV})
    (S : Stratum O F V) (hS0 : S.r = 0) (hS : S.IsSimple) (q : S.DefiningSequenceChoice)
    (ψ : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψ) {k l : ℕ} (hk : 1 ≤ k) (hkl : k ≤ l)
    {u v w z : G} (hu : u ∈ R[S] k) (hv : v ∈ R[S] k) (hw : w ∈ J[S,q] l) (hz : z ∈ J[S,q] l)
    (huw : u*w ∈ J[S,q] k) :
    adjointCharacterPair ψ S.b (((u*w : G) : A)-1) (((v*z : G) : A)-1) =
      adjointCharacterPair ψ S.b ((w : A)-1) ((z : A)-1) := by
  obtain ⟨_, _, _, _, _, _, _, hLayers⟩ := (hL F V S hS0 hS q).2.1
  have hpH := (hLayers k).2.2
  let dx := ((u * w : G) : A) - 1 - ((w : A) - 1)
  let dy := ((v * z : G) : A) - 1 - ((z : A) - 1)
  have hdx : dx ∈ 𝔥[S,q] k := translated_product_diff_mem hL S hS0 hS q hk hkl hu hw
  have hdy : dy ∈ 𝔥[S,q] k := translated_product_diff_mem hL S hS0 hS q hk hkl hv hz
  have hzJ : (z : A)-1 ∈ 𝔧[S,q] k :=
    (simpleJGroup_mem_iff_of_pos S hS0 hS q hk).mp (simpleJGroup_antitone S.chain S.n S.b q.tail hkl hz)
  have huwJ : ((u*w : G) : A)-1 ∈ 𝔧[S,q] k := (simpleJGroup_mem_iff_of_pos S hS0 hS q hk).mp huw
  have hdxJ : dx ∈ 𝔧[S,q] k := hpH hdx
  have hdyJ : dy ∈ 𝔧[S,q] k := hpH hdy
  have hdxval := (mem_simpleHLayer_iff_adjointCharacterPair S q hS0 hS ψ hψ hdxJ).mp hdx _ hzJ
  have hdyval := (mem_simpleHLayer_iff_adjointCharacterPair S q hS0 hS ψ hψ hdyJ).mp hdy _ huwJ
  have hdyval' : adjointCharacterPair ψ S.b (((u*w : G) : A)-1) dy = 1 := by
    rw [adjointCharacterPair_swap, hdyval, inv_one]
  have ex : ((u*w : G) : A)-1 = ((w : A)-1)+dx := by dsimp only [dx]; abel
  have ey : ((v*z : G) : A)-1 = ((z : A)-1)+dy := by dsimp only [dy]; abel
  rw [ey, adjointCharacterPair_add_right, hdyval', mul_one, ex,
    adjointCharacterPair_add_left, hdxval, mul_one]

private theorem scalar_eval
    (S : Stratum O F V) (hS0 : S.r = 0) (hS : S.IsSimple) (q : S.DefiningSequenceChoice)
    (ψ : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψ) (hs : elementAlgebra S.b = ⊥)
    {x y : G} {k i : ℕ} (hk : 1 ≤ k) {θ : H[S,q] (i+1) →* ℂˣ}
    (hdet : ∀ u v : G, u ∈ centralizerUnitGroup S.b → v ∈ centralizerUnitGroup S.b →
      ∀ hc : ⁅u,v⁆ ∈ H[S,q] (i+1), θ ⟨_, hc⟩ = 1)
    (hx : x ∈ J[S,q] k) (hy : y ∈ J[S,q] k) (hc : ⁅x,y⁆ ∈ H[S,q] (i+1)) :
    (θ ⟨_, hc⟩ : ℂ) = adjointCharacterPair ψ S.b ((x : A)-1) ((y : A)-1) := by
  have hxU := simpleJGroup_le_unitFiltration S.chain S.n S.b q.tail k hx
  have hyU := simpleJGroup_le_unitFiltration S.chain S.n S.b q.tail k hy
  have hxJ := (simpleJGroup_mem_iff_of_pos S hS0 hS q hk).mp hx
  have hyJ := (simpleJGroup_mem_iff_of_pos S hS0 hS q hk).mp hy
  have hxc := scalar_centralizes S hs (S.chain.unitFiltration_antitone (Nat.zero_le k) hxU)
  have hyc := scalar_centralizes S hs (S.chain.unitFiltration_antitone (Nat.zero_le k) hyU)
  have hxH : (x : A)-1 ∈ 𝔥[S,q] k := by
    change (x : A)-1 ∈ layer true S.chain S.n S.b q.tail k
    rw [layer_eq_endFiltration_of_scalar true _ _ _ _ k hs]
    exact hxU.2.2
  rw [hdet x y hxc hyc hc,
    (mem_simpleHLayer_iff_adjointCharacterPair S q hS0 hS ψ hψ hxJ).mp hxH _ hyJ, Units.val_one]

/-- For units at a common positive depth, the simple-character commutator is
computed by the additive adjoint product whenever the commutator depth reaches the domain. -/
theorem simpleCharacter_commutator_eq_adjointPair
    (hL : SimpleStratumLatticePropertiesStatement.{uF,uV})
    (hG : SimpleStratumGroupPropertiesStatement.{uF,uV})
    (hR : SimpleCharacterRelativeCommutatorLaws.{uF,uV})
    (ψ : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψ)
    (S : Stratum O F V) (hS0 : S.r = 0) (hS : S.IsSimple) (q : S.DefiningSequenceChoice)
    {i k : ℕ} (hi : (i : ℤ) < depth[S]) (hk : 1 ≤ k) (hip : i + 1 ≤ k + k)
    {θ : H[S,q] (i+1) →* ℂˣ} (hθ : θ ∈ C[ψ,S,q] i)
    {x y : G} (hx : x ∈ J[S,q] k) (hy : y ∈ J[S,q] k)
    (hc : ⁅x,y⁆ ∈ H[S,q] (i+1)) :
    (θ ⟨_, hc⟩ : ℂ) = adjointCharacterPair ψ S.b ((x : A)-1) ((y : A)-1) := by
  induction hsteps : q.steps using Nat.strong_induction_on generalizing S q i k x y with
  | h count ih =>
    obtain ⟨hnorm, hdet, hmix⟩ := hR F V ψ hψ S hS0 hS q i hi θ hθ
    by_cases hs : elementAlgebra S.b = ⊥
    · exact scalar_eval S hS0 hS q ψ hψ hs hk hdet hx hy hc
    have hd := depth_pos S hS0 hS
    have hj : (jcut[S] : ℤ) = simpleJCutoff depth[S] :=
      Int.toNat_of_nonneg (by unfold simpleJCutoff; omega)
    have hjpos : 1 ≤ jcut[S] := by
      have hpos : 1 ≤ simpleJCutoff depth[S] := by unfold simpleJCutoff; omega
      rw [← hj] at hpos
      exact_mod_cast hpos
    have evalHigh (l : ℕ) (hl : jcut[S] ≤ l) (hil : i + 1 ≤ l+l) (w z : G)
        (hw : w ∈ J[S,q] l) (hz : z ∈ J[S,q] l) (hc' : ⁅w,z⁆ ∈ H[S,q] (i+1)) :
        (θ ⟨_, hc'⟩ : ℂ) = adjointCharacterPair ψ S.b ((w : A)-1) ((z : A)-1) := by
      have hwU := simpleJGroup_le_unitFiltration S.chain S.n S.b q.tail l hw
      have hzU := simpleJGroup_le_unitFiltration S.chain S.n S.b q.tail l hz
      have hlInt : simpleJCutoff depth[S] ≤ (l : ℤ) := by
        rw [← hj]
        exact_mod_cast hl
      have hlPos : 1 ≤ l := hjpos.trans hl
      have hdl : depth[S] < (l : ℤ) + (l : ℤ) + (min l l : ℕ) := by
        simp only [min_self]
        unfold simpleJCutoff at hlInt
        omega
      by_cases hzero : q.steps = 0
      · have hdn := terminal_depth S q hzero
        have htail := (tail_nil_iff S q).mpr hzero
        have hlevel : (simpleHCutoff S.n).toNat ≤ l+l := by
          rw [← hdn]
          unfold simpleJCutoff at hlInt
          unfold simpleHCutoff
          omega
        rw [terminal_character_value ψ S.chain S.n S.b q.tail i htail hθ ⟨_, hc'⟩
          (S.chain.unitFiltration_antitone hlevel (LatticeChain.commutatorElement_mem_unitFiltration S.chain hwU hzU))]
        have hb : S.b ∈ S.chain.endFiltration (-S.n) := by
          apply (StratumEquivalence.mem_of_valuation_eq (m := -S.n) ?_).1
          exact hS.1.2
        exact elementCharacter_commutator_eq_adjointCharacterPair S.chain ψ hψ hb hwU hzU (hdn ▸ hdl)
      · obtain ⟨T, q', r, hchain, hn, hT0, hT, hrp, hrn, hcrit, hnext, hdiff, htail, hshort⟩ :=
          q.exists_suffix hS0 (Nat.pos_of_ne_zero hzero)
        have hdr := finiteCriticalDepth_eq_of_criticalExponent S.chain S.n S.b r hcrit
        have hdt : depth[S] < depth[T] := by
          rw [hchain, hn, hdr]
          exact lt_finiteCriticalDepth_of_criticalExponent_lt hrn hnext
        let a := max i (depth[S] / 2).toNat
        have hia : (a : ℤ) < depth[T] := by dsimp only [a]; omega
        have ha : a + 1 ≤ l+l := by dsimp only [a]; unfold simpleJCutoff at hlInt; omega
        have hex := approx_character_value ψ S.chain S.n S.b T.b q.tail q'.tail i htail hi hθ
        change ∃ η ∈ simpleCharacters ψ S.chain S.n T.b q'.tail a,
          characterAgreesOn (H[S,q] (a+1)) θ η (elementCharacter (traceCharacter ψ) (S.b-T.b)) at hex
        have hex' : ∃ η ∈ C[ψ,T,q'] a,
            characterAgreesOn (H[S,q] (a+1)) θ η (elementCharacter (traceCharacter ψ) (S.b-T.b)) := by
          rcases T with ⟨chain, n, r', b, hr', hb⟩
          change chain = S.chain at hchain
          change n = S.n at hn
          subst chain n
          exact hex
        obtain ⟨η, hη, hval⟩ := hex'
        have hJ : 𝔧[S,q] l = 𝔧[T,q'] l := layer_eq_suffix false hT0 hT q q' hchain hn hrp hrn
          hcrit hnext hdiff htail (by change simpleJCutoff r ≤ (l : ℤ); rwa [← hdr])
        have hJG : J[S,q] l = J[T,q'] l := by
          ext g
          rw [simpleJGroup_mem_iff_of_pos S hS0 hS q hlPos,
            simpleJGroup_mem_iff_of_pos T hT0 hT q' hlPos, hJ]
        have hcA := commutator_mem_HGroup hG S hS0 hS q (hjpos.trans hl) (hjpos.trans hl) ha hw hz
        obtain ⟨_, hB, he⟩ := hval ⟨_, hcA⟩
        change (θ ⟨⁅w,z⁆, _⟩ : ℂ) = (η ⟨⁅w,z⁆, hB⟩ : ℂ) *
          elementCharacter (traceCharacter ψ) (S.b-T.b) ⁅w,z⁆ at he
        rw [he, ih q'.steps (hsteps ▸ hshort) T hT0 hT q' hia (hjpos.trans hl) ha hη
          (hJG ▸ hw) (hJG ▸ hz) hB rfl,
          elementCharacter_commutator_eq_adjointCharacterPair S.chain ψ hψ hdiff hwU hzU (hdr ▸ hdl),
          ← adjointCharacterPair_add_param]
        rw [show T.b + (S.b-T.b) = S.b by abel]
    by_cases hjk : jcut[S] ≤ k
    · exact evalHigh k hjk hip x y hx hy hc
    · have hkj : k < jcut[S] := lt_of_not_ge hjk
      have hgrp := ((hG F V S hS0 hS q).2.1 hs).2 k (by omega)
      have hx' : x ∈ (R[S] k : Set G) * (J[S,q] jcut[S] : Set G) :=
        hgrp ▸ (show x ∈ (J[S,q] k : Set G) from hx)
      have hy' : y ∈ (R[S] k : Set G) * (J[S,q] jcut[S] : Set G) :=
        hgrp ▸ (show y ∈ (J[S,q] k : Set G) from hy)
      obtain ⟨u, hu, w, hw, rfl⟩ := Set.mem_mul.mp hx'
      obtain ⟨v, hv, z, hz, rfl⟩ := Set.mem_mul.mp hy'
      have hRleJ := (relativeUnitFiltration_le_simpleHGroup S.chain S.n S.b q.tail k).trans
        (((hG F V S hS0 hS q).2.2.2.1 k).1)
      have huJ := hRleJ hu
      have hvJ := hRleJ hv
      have hcomm {a b : G} (ha : a ∈ J[S,q] k) (hb : b ∈ J[S,q] k) :=
        commutator_mem_HGroup hG S hS0 hS q hk hk hip ha hb
      have hwJ := simpleJGroup_antitone S.chain S.n S.b q.tail hkj.le hw
      have hzJ := simpleJGroup_antitone S.chain S.n S.b q.tail hkj.le hz
      have hwv : θ ⟨_, hcomm hwJ hvJ⟩ = 1 := by
        rw [character_commutator_swap θ (hcomm hwJ hvJ) (hcomm hvJ hwJ),
          hmix k hk hkj hip v w hv hw (hcomm hvJ hwJ), inv_one]
      rw [character_commutator_mul_mul (hnorm k hu) (hnorm k hv)
        (hcomm hwJ hvJ) (hcomm hwJ hzJ) (hcomm huJ hvJ) (hcomm huJ hzJ) hwv
        (hdet u v hu.1 hv.1 _) (hmix k hk hkj hip u z hu hz _) hc,
        evalHigh jcut[S] le_rfl (by omega) w z hw hz (hcomm hwJ hzJ),
        adjointCharacterPair_mul_mul hL S hS0 hS q ψ hψ hk hkj.le hu hv hw hz hx]

end SimpleStratum

end Langlands.BushnellKutzko
