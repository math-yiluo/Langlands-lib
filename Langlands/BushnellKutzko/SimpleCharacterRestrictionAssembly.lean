import Langlands.BushnellKutzko.SimpleCharacterAdjacentRestriction
import Langlands.BushnellKutzko.SimpleCharacterPairsReindex
import Langlands.BushnellKutzko.SimpleCharacterRestrictionLow
import Langlands.BushnellKutzko.SimpleCharacterTwistMembership
import Langlands.BushnellKutzko.DefiningSequenceSuffix
import Langlands.BushnellKutzko.SimpleStratumLatticeInduction

/-! # Assembling the simple-character restriction theorem -/

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

noncomputable section

universe uF uV

section Successor

variable {F : Type uF} [Field F] [ValuativeRel F]
  {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

private def withParameterAtDepth (S : Stratum 𝒪[F] F V) (b : A) (r : ℤ)
    (h : r < S.n) (hb : (-S.n : WithTop ℤ) ≤ S.chain.valuation b) : Stratum 𝒪[F] F V :=
  ⟨S.chain, S.n, r, b, h, hb⟩

private structure CharacterSuccessor {S : Stratum 𝒪[F] F V} (q : S.DefiningSequenceChoice) where
  b : A
  depth : ℤ
  depth_pos : 0 < depth
  depth_lt : depth < S.n
  valuation_ge : (-S.n : WithTop ℤ) ≤ S.chain.valuation b
  simple : (withParameterAtDepth S b 0 (depth_pos.trans depth_lt) valuation_ge).IsSimple
  choice : (withParameterAtDepth S b 0 (depth_pos.trans depth_lt) valuation_ge).DefiningSequenceChoice
  critical : criticalExponent S.chain S.b = ((-depth : ℤ) : WithBot ℤ)
  successor_critical : criticalExponent S.chain b < ((-depth : ℤ) : WithBot ℤ)
  difference : S.b - b ∈ S.chain.endFiltration (-depth)
  tail : q.tail = b :: choice.tail
  shorter : choice.steps < q.steps
  group_eq : ∀ m : ℕ, depth / 2 ≤ (m : ℤ) →
    simpleHGroup S.chain S.n b choice.tail (m + 1) =
      simpleHGroup S.chain S.n S.b (b :: choice.tail) (m + 1)

private abbrev CharacterSuccessor.zero {S : Stratum 𝒪[F] F V} {q : S.DefiningSequenceChoice}
    (D : CharacterSuccessor q) : Stratum 𝒪[F] F V :=
  withParameterAtDepth S D.b 0 (D.depth_pos.trans D.depth_lt) D.valuation_ge

private abbrev CharacterSuccessor.approximation {S : Stratum 𝒪[F] F V}
    {q : S.DefiningSequenceChoice} (D : CharacterSuccessor q) : Stratum 𝒪[F] F V :=
  withParameterAtDepth S D.b D.depth D.depth_lt D.valuation_ge

private theorem CharacterSuccessor.depth_eq {S : Stratum 𝒪[F] F V}
    {q : S.DefiningSequenceChoice} (D : CharacterSuccessor q) :
    finiteCriticalDepth S.chain S.n S.b = D.depth :=
  finiteCriticalDepth_of_criticalExponent_eq _ _ _ _ D.critical

end Successor

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

private theorem characterSuccessor_exists {S : Stratum 𝒪[F] F V} (h0 : S.r = 0)
    (q : S.DefiningSequenceChoice) (hq : 0 < q.steps) : Nonempty (CharacterSuccessor q) := by
  obtain ⟨T, u, r, hL, hn, hT0, hT, hr, hrn, hc, hc', hdiff, htail, hshort⟩ :=
    q.exists_suffix h0 hq
  rcases T with ⟨L, n, t, γ, ht, hval⟩
  change L = S.chain at hL
  change n = S.n at hn
  change t = 0 at hT0
  subst L n t
  refine ⟨{ b := γ
            depth := r
            depth_pos := hr
            depth_lt := hrn
            valuation_ge := hval
            simple := hT
            choice := u
            critical := hc
            successor_critical := hc'
            difference := hdiff
            tail := htail
            shorter := hshort
            group_eq := fun m hm => ?_ }⟩
  have hlt : criticalExponent S.chain S.b < (0 : WithBot ℤ) := by
    rw [hc]
    exact WithBot.coe_lt_coe.mpr (by omega : -r < 0)
  have hseq := SimpleStratumLattice.sequence_of_choice S.chain q rfl hlt
  rw [htail] at hseq
  have hcut : SimpleStratumLattice.cutoff .H r ≤ ((m + 1 : ℕ) : ℤ) := by
    change r / 2 + 1 ≤ _
    omega
  have hLayer := hseq.high_eq (hr.trans hrn) hc .H hcut
  exact (simpleHGroup_eq_of_layer_eq S.chain S.n S.b γ (γ :: u.tail) u.tail (m + 1) hLayer).symm

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

private theorem CharacterSuccessor.reverse (hDet : IntertwinedUnitCharacterStatement.{uV,uV})
    (hGroups : SimpleStratumGroupPropertiesStatement.{uF,uV})
    (hCov : SimpleCharacterCovarianceStatement.{uF,uV})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    {S : Stratum 𝒪[F] F V} (h0 : S.r = 0) (hS : S.IsSimple) {q : S.DefiningSequenceChoice}
    (D : CharacterSuccessor q) {m : ℕ} (hm : D.depth / 2 ≤ (m : ℤ)) (hm' : (m : ℤ) < D.depth) :
    let C := simpleCharacters ψF S.chain S.n S.b (D.b :: D.choice.tail) m
    let C' := simpleCharacters ψF S.chain S.n D.b D.choice.tail m
    let τ := elementCharacterHom S.chain ψF hψ D.difference (by omega)
      (simpleHGroup_le_unitFiltration S.chain S.n D.b D.choice.tail (m + 1))
    ∀ θ ∈ C', characterTwistTransport (D.group_eq m hm) τ θ ∈ C := by
  intro C C' τ
  have hS' : D.approximation.IsSimple := ⟨D.simple.1, D.successor_critical⟩
  have hβ : S.b ∈ D.approximation.coset := D.difference
  let t := D.depth.toNat
  have ht : (t : ℤ) = D.depth := Int.toNat_of_nonneg D.depth_pos.le
  have htN : (t : ℤ) < D.zero.n := ht.symm ▸ D.depth_lt
  have hmN : (m : ℤ) < D.zero.n := hm'.trans D.depth_lt
  have htcrit : ((t : ℤ) : WithTop ℤ) < simpleCriticalDepth D.zero.chain D.zero.b := by
    rw [ht]
    exact simpleCriticalDepth_gt_of_criticalExponent_lt (L := S.chain) (β := D.b)
      D.successor_critical
  have hmcrit : ((m : ℤ) : WithTop ℤ) < simpleCriticalDepth D.zero.chain D.zero.b :=
    (WithTop.coe_le_coe.mpr (by omega : (m : ℤ) ≤ (t : ℤ))).trans_lt htcrit
  have hmt : t / 2 ≤ m := by omega
  have hformal := formalSelfIntertwining_subset_characterDoubleCoset D.approximation D.zero hS'
    D.choice D.depth_pos.le rfl rfl rfl
  have hnorm := ((hGroups F V S h0 hS q).2.2.1 (m + 1)).1
  rw [D.tail] at hnorm
  have hd : S.b - D.b ∈ S.chain.endFiltration (-finiteCriticalDepth S.chain S.n S.b) := by
    rw [D.depth_eq]
    exact D.difference
  exact simpleCharacters_reverse_twist_of_covariance hDet ψF hψ hS.1 hβ D.choice.tail m
    hd (by rwa [D.depth_eq]) (by rwa [D.depth_eq]) (D.group_eq m hm) hnorm
    (fun θ hθ g hg => hCov F V ψF hψ D.zero rfl D.simple D.choice m t hmN htN
      hmcrit htcrit hmt θ hθ g (hformal hg))

private theorem CharacterSuccessor.membership (hDet : IntertwinedUnitCharacterStatement.{uV,uV})
    (hGroups : SimpleStratumGroupPropertiesStatement.{uF,uV})
    (hCov : SimpleCharacterCovarianceStatement.{uF,uV})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    {S : Stratum 𝒪[F] F V} (h0 : S.r = 0) (hS : S.IsSimple) {q : S.DefiningSequenceChoice}
    (D : CharacterSuccessor q) {m : ℕ} (hm : D.depth / 2 ≤ (m : ℤ)) :
    let C := simpleCharacters ψF S.chain S.n S.b (D.b :: D.choice.tail) m
    let C' := simpleCharacters ψF S.chain S.n D.b D.choice.tail m
    let τ := elementCharacterHom S.chain ψF hψ D.difference (by omega)
      (simpleHGroup_le_unitFiltration S.chain S.n D.b D.choice.tail (m + 1))
    ∀ θ, θ ∈ C' ↔ characterTwistTransport (D.group_eq m hm) τ θ ∈ C := by
  have hd : S.b - D.b ∈ S.chain.endFiltration (-finiteCriticalDepth S.chain S.n S.b) := by
    rw [D.depth_eq]
    exact D.difference
  exact simpleCharacters_twist_cons_iff_of_reverse S.chain ψF hψ S.n S.b D.b D.choice.tail m
    hd (by rwa [D.depth_eq]) (D.group_eq m hm)
    (fun h => D.reverse hDet hGroups hCov ψF hψ h0 hS hm (by rwa [D.depth_eq] at h))

private theorem adjacent_restriction_of_inputs (hDet : IntertwinedUnitCharacterStatement.{uV,uV})
    (hGroups : SimpleStratumGroupPropertiesStatement.{uF,uV})
    (hCov : SimpleCharacterCovarianceStatement.{uF,uV})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    (S : Stratum 𝒪[F] F V) (h0 : S.r = 0) (hS : S.IsSimple) (q : S.DefiningSequenceChoice) :
    ∀ m : ℕ, (m : ℤ) + 1 < S.n →
      (simpleCharacterRestriction S q (Nat.le_succ m)) '' simpleCharacters ψF S.chain S.n S.b q.tail m =
        simpleCharacters ψF S.chain S.n S.b q.tail (m + 1) := by
  induction hsize : q.steps using Nat.strong_induction_on generalizing S with
  | h k ih =>
    intro m hm
    let r := finiteCriticalDepth S.chain S.n S.b
    let d := (r / 2).toNat
    by_cases hm' : m + 1 ≤ d
    · exact (simpleCharacterRestriction_low_of_groupProperties hGroups ψF h0 hS q
        (Nat.le_succ m) hm').1
    have hcut : r / 2 ≤ (m : ℤ) := by dsimp [d] at hm'; omega
    by_cases hq : q.steps = 0
    · have htail : q.tail = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa [Stratum.DefiningSequenceChoice.tail] using hq
      have hr : r = S.n := q.finiteCriticalDepth_of_tail_nil htail
      exact simpleCharacterRestriction_adjacent_high hDet ψF hψ q (hr ▸ hcut)
    obtain ⟨D⟩ := characterSuccessor_exists h0 q (Nat.pos_of_ne_zero hq)
    have hd : S.b - D.b ∈ S.chain.endFiltration (-r) := by
      change S.b - D.b ∈ S.chain.endFiltration (-finiteCriticalDepth S.chain S.n S.b)
      rw [D.depth_eq]
      exact D.difference
    have hcut' : D.depth / 2 ≤ (m : ℤ) := by rwa [← D.depth_eq]
    have hEq (j : ℕ) (hj : m ≤ j) : simpleHGroup S.chain S.n D.b D.choice.tail (j + 1) =
        simpleHGroup S.chain S.n S.b (D.b :: D.choice.tail) (j + 1) :=
      D.group_eq j (by omega)
    have hred : D.choice.steps < k := hsize ▸ D.shorter
    have hImage := ih D.choice.steps hred D.zero rfl D.simple D.choice rfl m hm
    change (fun χ : simpleHGroup S.chain S.n S.b q.tail (m + 1) →* ℂˣ =>
      χ.comp (Subgroup.inclusion (simpleHGroup_antitone S.chain S.n S.b q.tail
        (Nat.succ_le_succ (Nat.le_succ m))))) '' simpleCharacters ψF S.chain S.n S.b q.tail m =
          simpleCharacters ψF S.chain S.n S.b q.tail (m + 1)
    rw [D.tail]
    exact simpleCharacters_adjacent_cons_of_twist S.chain ψF hψ S.n S.b D.b D.choice.tail m
      hd hcut hEq (fun j hj hj' => D.reverse hDet hGroups hCov ψF hψ h0 hS
        (by omega) (by rwa [D.depth_eq] at hj')) hImage

private theorem critical_approximation_twist_of_inputs (hDet : IntertwinedUnitCharacterStatement.{uV,uV})
    (hGroups : SimpleStratumGroupPropertiesStatement.{uF,uV})
    (hCov : SimpleCharacterCovarianceStatement.{uF,uV})
    (hChoice : SimpleCharacterChoiceStatement.{uF,uV})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    (S : Stratum 𝒪[F] F V) (h0 : S.r = 0) (hS : S.IsSimple) (q : S.DefiningSequenceChoice) :
    let r := finiteCriticalDepth S.chain S.n S.b
    ∀ U : Stratum 𝒪[F] F V, S.IsCriticalApproximation U → ∀ u : U.DefiningSequenceChoice,
      ∀ m : ℕ, r / 2 ≤ (m : ℤ) → (m : ℤ) < r →
        let H := simpleHGroup S.chain S.n S.b q.tail (m + 1)
        let H' := simpleHGroup U.chain U.n U.b u.tail (m + 1)
        let C := simpleCharacters ψF S.chain S.n S.b q.tail m
        let C' := simpleCharacters ψF U.chain U.n U.b u.tail m
        H = H' ∧ ∃ e : C ≃ C', ∀ θ : C,
          characterAgreesOn H' (e θ).val θ.val
            (fun g => (elementCharacter (traceCharacter ψF) (S.b - U.b) g)⁻¹) := by
  intro r U hU u m hm hm' H H' C C'
  obtain ⟨hUorder, hUn, hUs, hUcrit, hUdiff⟩ := hU
  have hrU : r = U.r := finiteCriticalDepth_of_criticalExponent_eq _ _ _ _ hUcrit
  have hlt : r < S.n := by rw [hrU, ← hUn]; exact U.r_lt_n
  have hpositive : 0 < q.steps := by
    by_contra hn
    have htail : q.tail = [] := by
      apply List.eq_nil_of_length_eq_zero
      simp [Stratum.DefiningSequenceChoice.tail, show q.steps = 0 by omega]
    have he : r = S.n := q.finiteCriticalDepth_of_tail_nil htail
    omega
  obtain ⟨D⟩ := characterSuccessor_exists h0 q hpositive
  have hrD : r = D.depth := D.depth_eq
  have hDU : U.r = D.depth := hrU.symm.trans hrD
  have hcut : D.depth / 2 ≤ (m : ℤ) := hrD ▸ hm
  have hCrit : (U.r : WithTop ℤ) < simpleCriticalDepth D.zero.chain D.zero.b := by
    rw [hDU]
    exact simpleCriticalDepth_gt_of_criticalExponent_lt (L := S.chain) (β := D.b)
      D.successor_critical
  have hCritm : ((m : ℤ) : WithTop ℤ) < simpleCriticalDepth D.zero.chain D.zero.b :=
    (WithTop.coe_le_coe.mpr (by omega : (m : ℤ) ≤ U.r)).trans_lt hCrit
  have hSub : U.b - D.b ∈ S.chain.endFiltration (-U.r) := by
    have hsum : U.b - D.b = (U.b - S.b) + (S.b - D.b) := by abel
    rw [hsum]
    exact add_mem hUdiff (hDU.symm ▸ D.difference)
  obtain ⟨hDomain, hCharacters⟩ := (hChoice F V ψF hψ D.zero rfl D.simple D.choice).2
    U hUorder hUn hUs (by omega) hCrit hSub u m (by omega) (hm'.trans hlt) hCritm
  have hH : simpleHGroup S.chain S.n D.b D.choice.tail (m + 1) = H := by
    change _ = simpleHGroup S.chain S.n S.b q.tail (m + 1)
    rw [D.tail]
    exact D.group_eq m hcut
  refine ⟨hH.symm.trans hDomain, ?_⟩
  change ∃ e : (simpleCharacters ψF S.chain S.n S.b q.tail m) ≃ C', ∀ θ,
    characterAgreesOn H' (e θ).val θ.val
      (fun g => (elementCharacter (traceCharacter ψF) (S.b - U.b) g)⁻¹)
  rw [D.tail]
  let τ₁ := elementCharacterHom S.chain ψF hψ D.difference (by omega :
    1 ≤ -D.depth + (((m + 1 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ)))
    (simpleHGroup_le_unitFiltration S.chain S.n D.b D.choice.tail (m + 1))
  let τ₂ := elementCharacterHom S.chain ψF hψ hSub (by omega :
    1 ≤ -U.r + (((m + 1 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ)))
    (simpleHGroup_le_unitFiltration S.chain S.n D.b D.choice.tail (m + 1))
  exact exists_characterTwist_equiv_of_intermediate ψF S.b D.b U.b (D.group_eq m hcut) hDomain
    _ _ _ τ₁ τ₂ (fun _ => rfl) (fun _ => rfl)
    (D.membership hDet hGroups hCov ψF hψ h0 hS hcut) hCharacters

/-- High-index existence, cutoff restriction, covariance and choice coherence give the
restriction, twisting and nonemptiness theorem by induction along the defining sequence. -/
theorem simpleCharacterRestriction_of_component_theorems
    (hDet : IntertwinedUnitCharacterStatement.{uV,uV})
    (hGroups : SimpleStratumGroupPropertiesStatement.{uF,uV})
    (hCov : SimpleCharacterCovarianceStatement.{uF,uV})
    (hChoice : SimpleCharacterChoiceStatement.{uF,uV}) :
    SimpleCharacterRestrictionStatement.{uF,uV} := by
  intro F _ _ _ _ V _ _ ψF hψ S h0 hS q
  dsimp only
  have hAdj := adjacent_restriction_of_inputs hDet hGroups hCov ψF hψ S h0 hS q
  refine ⟨fun m hm _ => simpleCharacters_high_singleton_of_detCriterion hDet ψF hψ q hm,
    ?_, critical_approximation_twist_of_inputs hDet hGroups hCov hChoice ψF hψ S h0 hS q,
    hAdj, simpleCharacterRestriction_nonempty_of_adjacent hDet ψF hψ h0 q hAdj⟩
  intro _ m hm _
  exact simpleCharacterRestriction_low_of_groupProperties hGroups ψF h0 hS q hm le_rfl

end

end Langlands.BushnellKutzko
