import Langlands.BushnellKutzko.SimpleLowerHGroup
import Langlands.BushnellKutzko.SimpleCharacterRelativeCommutators
import Langlands.BushnellKutzko.SimpleStratumPairingDual
import Langlands.BushnellKutzko.BlockLatticeCharacter
import Langlands.BushnellKutzko.PairingTransfer

/-! # Jacquet transfer to the depth-one lower enlargement -/

noncomputable section

open ValuativeRel
open scoped Pointwise commutatorElement

namespace Langlands.BushnellKutzko.SplitBlocks

universe uF uV uW

local notation "H[" S "," q "]" => simpleHGroup (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "J[" S "," q "]" => simpleJGroup (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "Jₗ[" S "," q "]" => simpleJLayer (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)

private theorem relativeCommutators : SimpleCharacterRelativeCommutatorLaws.{uF,uV} := by
  apply SimpleStratum.relativeCommutatorLaws_of_mixedJ simpleStratumGroupProperties
  intro F _ _ _ _ V _ _ ψ hψ S h0 hs q r i k l hcrit hi hir hk hl hkl htrace θ hθ x y hx hy
  exact simpleCharacterMixedJCommutator ψ hψ S h0 hs q hcrit hi hir hk hl hkl htrace hθ hx hy

/-- Isotypic transfer from `H^1` to its lower enlargement by the adjoint pairing. -/
def SimpleLowerHTransferStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (V : Type uV) [AddCommGroup V] [Module F V]
    (S : Stratum 𝒪[F] F V) (_h0 : S.r = 0) (_hs : S.IsSimple) (q : S.DefiningSequenceChoice)
    (e₁ e₂ : Module.End F V) (he₁₂ : e₁ * e₂ = 0) (he₂₁ : e₂ * e₁ = 0)
    (_he₁₁ : e₁ * e₁ = e₁) (_he₂₂ : e₂ * e₂ = e₂)
    (_he₁ : e₁ ∈ centralizerLattice S.chain S.b 0)
    (_he₂ : e₂ ∈ centralizerLattice S.chain S.b 0)
    (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    let G := (Module.End F V)ˣ
    let K := simpleLowerHGroup S q he₁₂
    ∀ (θ : H[S,q] 1 →* ℂˣ), θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail 0 →
    ∀ (η : K →* ℂˣ),
    (∀ (d : simpleLowerJGroup S q he₁₂) (h : H[S,q] 1) (hk : (d : G) * (h : G) ∈ K),
        η ⟨(d : G) * (h : G), hk⟩ = θ h) →
    ∀ b : Module.End F V, b ∈ S.chain.endFiltration (-1) →
    ∀ (ϑ : K →* ℂˣ),
    (∀ k, (ϑ k : ℂ) = (η k : ℂ) * elementCharacter (traceCharacter ψF) b (k : G)) →
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W)
      (M : Subgroup G), M ≤ blockUnipotent e₁ e₂ he₂₁ ⊤ →
    ∀ v : W, (∀ k : K, (k : G) ∈ H[S,q] 1 → ρ k v = (ϑ k : ℂ) • v) →
    v ∉ Jacquet.relations ρ M →
    ∃ w : W, (∀ k : K, ρ k w = (ϑ k : ℂ) • w) ∧ w ∉ Jacquet.relations ρ M

/-- The adjoint commutator pairing gives all the character ratios used to
average the conjugates of the lower extension. -/
theorem exists_isotypic_of_simpleLowerHCharacter : SimpleLowerHTransferStatement.{uF,uV,uW} := by
  intro F _ _ _ _ V _ _ S h0 hs q e₁ e₂ he₁₂ he₂₁ he₁₁ he₂₂ he₁ he₂ ψF hψ G K
    θ hθ η hη b hb ϑ hϑ W _ _ ρ M hM v hv hvM
  classical
  let A := Module.End F V
  let L := S.chain
  have := L.finiteDimensional
  let H := H[S,q] 1
  let J := J[S,q] 1
  let D := simpleLowerJGroup S q he₁₂
  let P := Jₗ[S,q] 1
  let Z := latticeQuotient L P S.n
  have hKJ : K ≤ J := simpleLowerHGroup_le_simpleJGroup S h0 hs q he₁₂
  have hKU : K ≤ L.unitFiltration 1 := hKJ.trans (simpleJGroup_le_unitFiltration L S.n S.b q.tail 1)
  have hHK : H ≤ K := le_sup_right
  have hηH (h : H) : η ⟨(h : G), hHK h.2⟩ = θ h := by
    have h := hη (1 : D) h (by simpa only [Subgroup.coe_one, one_mul] using hHK h.2)
    simpa only [Subgroup.coe_one, one_mul] using h
  obtain ⟨N, hN, hdeep⟩ := simpleCharacter_trivial_on_deep_units L S.n hψ S.b q.tail 0 hθ
  have hUH : L.unitFiltration N ≤ H := fun g hg => (hdeep g hg).choose
  let : (L.unitFiltration N).IsFiniteRelIndex (L.unitFiltration 1) := by
    apply Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
    exact L.unitFiltration_finiteIndex_in_one k
  let : H.IsFiniteRelIndex (L.unitFiltration 1) :=
    Subgroup.isFiniteRelIndex_of_le_left (L.unitFiltration 1) hUH
  let : H.IsFiniteRelIndex K := Subgroup.isFiniteRelIndex_of_le_right H hKU
  let : Fintype (K ⧸ H.subgroupOf K) := Subgroup.fintypeQuotientOfFiniteIndex
  have hn : 0 < S.n := by have := S.r_lt_n; omega
  have hP0 : P ≤ L.endFiltration 0 := fun _ hx => L.endFiltration_antitone (by norm_num) hx.2
  have : Finite Z := finite_latticeQuotient L hP0 hn.le
  let : Fintype Z := Fintype.ofFinite Z
  have hJproj {e x : A} (he : e ∈ centralizerLattice L S.b 0) (hx : x ∈ P) :
      e * x ∈ P ∧ x * e ∈ P := by
    have hL := (simpleStratumLatticeProperties F V S h0 hs q).2.1
    have heJ := hL.2.2.2.2.2.1 (hL.2.2.2.2.1 he)
    have hI := (hL.2.2.2.2.2.2.2 1).2.1
    exact ⟨hI.2.1 (Submodule.mul_mem_mul heJ hx), hI.2.2 (Submodule.mul_mem_mul hx heJ)⟩
  have hrep : Function.Surjective (Submodule.Quotient.mk : P → Z) := Submodule.Quotient.mk_surjective _
  choose y hy using hrep
  let g (a : Z) := blockUnit e₁ e₂ he₂₁ (y a : A)
  have hgval (a : Z) : ((g a : G) : A) - 1 = e₁ * (y a : A) * e₂ := by
    dsimp only [g]
    rw [blockUnit_val, add_sub_cancel_left]
  have hgJ (a : Z) : g a ∈ J := by
    apply (simpleJGroup_mem_iff_of_pos S h0 hs q le_rfl).mpr
    rw [hgval]
    exact (hJproj he₂ (hJproj he₁ (y a).2).1).2
  have hnorm (a : Z) (k : G) (hk : k ∈ K) : g a * k * (g a)⁻¹ ∈ K :=
    simpleLowerHGroup_conj_mem S h0 hs q he₁₂ (hgJ a) hk
  have hnorm' (a : Z) (k : G) (hk : k ∈ K) : (g a)⁻¹ * k * g a ∈ K := by
    simpa only [inv_inv] using simpleLowerHGroup_conj_mem S h0 hs q he₁₂ (J.inv_mem (hgJ a)) hk
  have hβ : S.b ∈ L.endFiltration (-S.n) := by
    apply (StratumEquivalence.mem_of_valuation_eq (m := -S.n) ?_).1
    simpa only [WithTop.LinearOrderedAddCommGroup.coe_neg] using hs.1.2
  let w (k : K) := adjointMap 𝒪[F] S.b (((k : G) : A) - 1)
  have hw (k : K) : w k ∈ L.endFiltration (1 - S.n) := by
    have hx : (((k : G) : A) - 1) ∈ L.endFiltration 1 := (hKU k.2).2.2
    change S.b * (((k : G) : A) - 1) - (((k : G) : A) - 1) * S.b ∈ _
    have hl := L.mul_mem_endFiltration hβ hx
    have hr := L.mul_mem_endFiltration hx hβ
    rw [show 1 - S.n = -S.n + 1 by ring]
    exact sub_mem hl (by simpa only [add_comm] using hr)
  let Φ (k : K) : AddChar Z ℂ := latticeBlockCharacter L hψ P S.n he₁.1 he₂.1 (hw k)
  have hΦ (k : K) (t : P) : Φ k (Submodule.Quotient.mk t) =
      adjointCharacterPair ψF S.b (((k : G) : A) - 1) (e₁ * (t : A) * e₂) := by
    rw [latticeBlockCharacter_mk, adjointCharacterPair, traceCharacter_apply, traceCharacter_apply,
      LinearMap.trace_mul_comm F (e₁ * (t : A) * e₂)]
    rfl
  have hΦ' (k : K) (t : P) : Φ k (Submodule.Quotient.mk t) =
      adjointCharacterPair ψF S.b (e₂ * (((k : G) : A) - 1) * e₁) t := by
    let x : A := (k : G) - 1
    have ha : adjointMap F S.b (e₂ * x * e₁) = e₂ * adjointMap F S.b x * e₁ := by
      simp only [StratumEquivalence.adjointMap_apply]
      calc
        S.b * (e₂ * x * e₁) - (e₂ * x * e₁) * S.b =
          (S.b * e₂) * x * e₁ - e₂ * x * (e₁ * S.b) := by noncomm_ring
        _ = _ := by
          rw [commute_of_mem_centralizerLattice he₂, ← commute_of_mem_centralizerLattice he₁]
          noncomm_ring
    rw [latticeBlockCharacter_mk, adjointCharacterPair, traceCharacter_apply, traceCharacter_apply]
    change ψF (LinearMap.trace F V (e₁ * (t : A) * e₂ * w k)) =
      ψF (LinearMap.trace F V (adjointMap F S.b (e₂ * x * e₁) * t))
    rw [ha, show e₁ * (t : A) * e₂ * w k = (e₁ * (t : A)) * (e₂ * w k) by noncomm_ring,
      LinearMap.trace_mul_comm F (e₁ * (t : A))]
    congr 2
  refine Jacquet.exists_isotypic_not_mem_relations_of_addChar (𝒦 := H) ρ M ϑ g Φ hnorm hnorm' ?_ ?_ ?_ hv hvM
  · intro a k
    have hkJ := hKJ k.2
    have hc₂ := SimpleStratum.commutator_mem_HGroup simpleStratumGroupProperties S h0 hs q
      (k := 1) (l := 1) (p := 2) le_rfl le_rfl le_rfl (hgJ a) hkJ
    have hc : ⁅g a, (k : G)⁆ ∈ H := simpleHGroup_antitone L S.n S.b q.tail (by norm_num) hc₂
    let cH : H := ⟨_, hc⟩
    let cK : K := ⟨_, hHK hc⟩
    have ht : elementCharacter (traceCharacter ψF) b (cK : G) = 1 :=
      elementCharacter_eq_one_of_depth L ψF hψ hb (by norm_num)
        (simpleHGroup_le_unitFiltration L S.n S.b q.tail 2 hc₂)
    have hfac : (⟨_, hnorm a k k.2⟩ : K) = cK * k := by
      apply Subtype.ext
      simp [cK, commutatorElement_def]
    have heval : (θ cH : ℂ) = adjointCharacterPair ψF S.b (((g a : G) : A) - 1) (((k : G) : A) - 1) :=
      SimpleStratum.simpleCharacter_commutator_eq_adjointPair simpleStratumLatticeProperties
        simpleStratumGroupProperties relativeCommutators ψF hψ S h0 hs q
        (i := 0) (k := 1) (SimpleStratum.depth_pos S h0 hs) le_rfl (by norm_num) hθ (hgJ a) hkJ hc
    have hratio : Φ k a = (θ cH : ℂ)⁻¹ := by
      rw [← hy a, hΦ, adjointCharacterPair_swap ψF S.b, heval, hgval]
    rw [hfac, map_mul, Units.val_mul, hϑ cK, ht, mul_one, hηH cH, hratio, mul_right_comm,
      mul_inv_cancel₀ (Units.ne_zero _), one_mul]
  · intro k
    have hxJ := (simpleJGroup_mem_iff_of_pos S h0 hs q le_rfl).mp (hKJ k.2)
    have hcorner := (hJproj he₁ (hJproj he₂ hxJ).1).2
    rw [mem_simpleHGroup_iff_lowerCorner_of_mem_simpleLowerHGroup S h0 hs q he₁₂ he₁ he₂ k.2,
      SimpleStratum.mem_simpleHLayer_iff_adjointCharacterPair S q h0 hs ψF hψ hcorner]
    constructor
    · intro hz t ht
      rw [← hΦ' k ⟨t, ht⟩, hz, AddChar.zero_apply]
    · intro h
      ext a
      rw [← hy a, hΦ', h _ (y a).2, AddChar.zero_apply]
  · intro a m hm
    have hcomm : g a * m = m * g a :=
      blockUnipotent_commute (blockUnit_mem he₂₁ he₁₁ he₂₂ (y a : A)) (hM hm)
    rwa [inv_inv, mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]

end Langlands.BushnellKutzko.SplitBlocks
