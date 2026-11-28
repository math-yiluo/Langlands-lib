import Langlands.BushnellKutzko.SimpleCharacterRelativeDeterminant
import Langlands.BushnellKutzko.SimpleCharacterRestrictionHigh
import Langlands.BushnellKutzko.NormalizerProof
import Langlands.BushnellKutzko.SubfieldOrderProof

/-! # Existence at the high indices -/

open ValuativeRel

namespace Langlands.BushnellKutzko

noncomputable section

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

private abbrev IsNormalizedParameter (L : LatticeChain 𝒪[F] F V) (β : A) : Prop :=
  ∃ hE : IsField (elementAlgebra β),
    letI := hE.toField
    ∀ a : (elementAlgebra β)ˣ, subfieldUnits F (elementAlgebra β) V a ∈ L.stabilizer

private theorem factorsThroughCentralizerDet_of_trace_values
    (hIntw : IntertwinedUnitCharacterStatement.{uV,uV}) (L : LatticeChain 𝒪[F] F V)
    (ψF : AddChar F ℂ) {b : A} (hn : IsNormalizedParameter L b) {k : ℕ} (hk : 1 ≤ k)
    (θ : L.unitFiltration k →* ℂˣ)
    (hθ : ∀ g : L.unitFiltration k, (θ g : ℂ) = elementCharacter (traceCharacter ψF) b g) :
    factorsThroughCentralizerDet b θ := by
  refine factorsThroughCentralizerDet_of_relative_intertwining hIntw L hn hk le_rfl inf_le_right θ ?_
  intro x hx g hg
  apply Units.ext
  rw [hθ, hθ]
  exact elementCharacter_conj_of_centralizer ψF hx g

private theorem unitFiltration_normalized_by_relative_order (L : LatticeChain 𝒪[F] F V)
    (β : A) (k : ℕ) : relativeOrderNormalizer L β ≤ Subgroup.normalizer (L.unitFiltration k : Set G) := by
  rw [(normalizer F V L).2.2.1 k]
  exact inf_le_right

private theorem simpleCharacters_high_exists_of_cutoffs (hDet : IntertwinedUnitCharacterStatement.{uV,uV})
    (L : LatticeChain 𝒪[F] F V) (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    (n : ℤ) (m : ℕ) (hm : n / 2 ≤ (m : ℤ)) (β : A) (tail : List A)
    (hdepth : ∀ x ∈ β :: tail, finiteCriticalDepth L n x ≤ n)
    (hstep : (β :: tail).IsChain
      (fun x y => x - y ∈ L.endFiltration (-finiteCriticalDepth L n x)))
    (hparameters : ∀ x ∈ β :: tail, IsNormalizedParameter L x ∧ x ∈ L.endFiltration (-n)) :
    (simpleCharacters ψF L n β tail m).Nonempty := by
  have hcut : simpleHCutoff n ≤ ((m + 1 : ℕ) : ℤ) := by unfold simpleHCutoff; omega
  have hdouble : 1 ≤ -n + (((m + 1 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ)) := by omega
  have hex (a : A) (t : List A) (hd : ∀ x ∈ a :: t, finiteCriticalDepth L n x ≤ n)
      (ha : IsNormalizedParameter L a ∧ a ∈ L.endFiltration (-n)) :
      ∃ θ : simpleHGroup L n a t (m + 1) →* ℂˣ,
        (∀ g, (θ g : ℂ) = elementCharacter (traceCharacter ψF) a g) ∧
        factorsThroughCentralizerDet a θ ∧
        (relativeOrderNormalizer L a : Set G) ⊆ characterNormalizer θ := by
    have hH := simpleHGroup_eq_unitFiltration_of_cutoffs L n (m + 1) hcut a t hd
    have hn := unitFiltration_normalized_by_relative_order L a (m + 1)
    let θ := elementCharacterHom L ψF hψ ha.2 hdouble
      (simpleHGroup_le_unitFiltration L n a t (m + 1))
    have hv (g : simpleHGroup L n a t (m + 1)) :
        (θ g : ℂ) = elementCharacter (traceCharacter ψF) a g := rfl
    refine ⟨θ, hv, ?_, characterNormalizer_of_trace_values ψF inf_le_left (hH.symm ▸ hn) hv⟩
    exact (show ∀ χ : simpleHGroup L n a t (m + 1) →* ℂˣ,
        (∀ g, (χ g : ℂ) = elementCharacter (traceCharacter ψF) a g) →
          factorsThroughCentralizerDet a χ from hH.symm ▸
      factorsThroughCentralizerDet_of_trace_values hDet L ψF ha.1 (Nat.succ_pos m)) θ hv
  induction tail generalizing β with
  | nil =>
    obtain ⟨θ, hv, hdet, _⟩ := hex β [] hdepth (hparameters β (List.mem_cons_self ..))
    exact ⟨θ, by rw [simpleCharacters]; exact ⟨fun g _ => hv g, hdet⟩⟩
  | cons γ rest ih =>
    have hdepth' : ∀ x ∈ γ :: rest, finiteCriticalDepth L n x ≤ n :=
      fun x hx => hdepth x (List.mem_cons_of_mem β hx)
    have hparams' : ∀ x ∈ γ :: rest, IsNormalizedParameter L x ∧ x ∈ L.endFiltration (-n) :=
      fun x hx => hparameters x (List.mem_cons_of_mem β hx)
    obtain ⟨hdiff, hrest⟩ := List.isChain_cons_cons.mp hstep
    obtain ⟨θ, hv, hdet, hnorm⟩ := hex β (γ :: rest) hdepth
      (hparameters β (List.mem_cons_self ..))
    obtain ⟨θ₀, hθ₀⟩ := ih γ hdepth' hrest hparams'
    have hgβ := simpleHGroup_eq_unitFiltration_of_cutoffs L n (m + 1) hcut β (γ :: rest) hdepth
    have hgγ := simpleHGroup_eq_unitFiltration_of_cutoffs L n (m + 1) hcut γ rest hdepth'
    have hH := hgβ.trans hgγ.symm
    have hmax : max m (finiteCriticalDepth L n β / 2).toNat = m := by
      have hβ := hdepth β (List.mem_cons_self ..)
      apply max_eq_left
      omega
    refine ⟨θ, ?_⟩
    by_cases hm' : (m : ℤ) < finiteCriticalDepth L n β
    · simp only [simpleCharacters, ite_eq_left hm']
      rw [hmax]
      refine ⟨hdet, hnorm, θ₀, hθ₀, fun g => ?_⟩
      have hg₀ : (g : G) ∈ simpleHGroup L n γ rest (m + 1) := hH ▸ g.prop
      refine ⟨g.prop, hg₀, ?_⟩
      rw [hv, simpleCharacters_high_values_of_cutoffs L ψF hψ n m hm γ rest hdepth' hrest hθ₀ ⟨g, hg₀⟩]
      simp only [elementCharacter_apply, ← AddChar.map_add_eq_mul]
      congr 1
      noncomm_ring
    · simp only [simpleCharacters, ite_eq_right hm']
      refine ⟨θ₀, hθ₀, hH, fun g => ?_⟩
      have hg₀ : (g : G) ∈ simpleHGroup L n γ rest (m + 1) := hH ▸ g.prop
      refine ⟨g.prop, hg₀, ?_⟩
      rw [hv, simpleCharacters_high_values_of_cutoffs L ψF hψ n m hm γ rest hdepth' hrest hθ₀ ⟨g, hg₀⟩,
        mul_one]
      have hgU : (g : G) ∈ L.unitFiltration (m + 1) := hgβ ▸ g.prop
      have hzero := elementCharacter_eq_one_of_depth L ψF hψ hdiff
        (by omega : 1 ≤ -finiteCriticalDepth L n β + ((m + 1 : ℕ) : ℤ)) hgU
      have he : elementCharacter (traceCharacter ψF) β g =
          elementCharacter (traceCharacter ψF) γ g * elementCharacter (traceCharacter ψF) (β - γ) g := by
        simp only [elementCharacter_apply, ← AddChar.map_add_eq_mul]
        congr 1
        noncomm_ring
      rw [he, hzero, mul_one]

private theorem definingParameters_normalized {S : Stratum 𝒪[F] F V}
    (q : S.DefiningSequenceChoice) :
    ∀ x ∈ S.b :: q.tail, IsNormalizedParameter S.chain x ∧ x ∈ S.chain.endFiltration (-S.n) := by
  have hterms (i : Fin (q.steps + 1)) : IsNormalizedParameter S.chain (q.terms i).b ∧
      (q.terms i).b ∈ S.chain.endFiltration (-S.n) := by
    let T := q.terms i
    obtain ⟨horder, hn, hS⟩ := q.isDefiningSequence.2.1 i
    have hf := StratumEquivalence.endFiltration_eq_of_eq
      (congrArg Subalgebra.toSubmodule horder)
    have hunit : T.chain.unitFiltration 0 = S.chain.unitFiltration 0 := by
      ext x
      simp only [LatticeChain.mem_unitFiltration_zero, show T.chain.order = S.chain.order from horder]
    have hnorm : T.chain.stabilizer = S.chain.stabilizer := by
      rw [← (normalizer F V T.chain).2.2.1 0, ← (normalizer F V S.chain).2.2.1 0, hunit]
    obtain ⟨⟨hE, hstab⟩, hval⟩ := hS.1
    refine ⟨⟨hE, fun a => hnorm ▸ hstab a⟩, ?_⟩
    rw [← hn, ← hf]
    exact (StratumEquivalence.mem_of_valuation_eq hval).1
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · simpa only [q.firstElement] using hterms 0
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact hterms i.succ

/-- The high-index singleton follows from the determinant criterion for the relative
unit filtration. -/
theorem simpleCharacters_high_singleton_of_detCriterion (hDet : IntertwinedUnitCharacterStatement.{uV,uV})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    {S : Stratum 𝒪[F] F V} (q : S.DefiningSequenceChoice) {m : ℕ} (hm : S.n / 2 ≤ (m : ℤ)) :
    let H := simpleHGroup S.chain S.n S.b q.tail (m + 1)
    let C := simpleCharacters ψF S.chain S.n S.b q.tail m
    H = S.chain.unitFiltration (m + 1) ∧ ∃ θ : H →* ℂˣ, C = {θ} ∧
      ∀ g : H, (θ g : ℂ) = elementCharacter (traceCharacter ψF) S.b g := by
  intro H C
  obtain ⟨θ, hθ⟩ := simpleCharacters_high_exists_of_cutoffs hDet S.chain ψF hψ S.n m hm S.b q.tail
    q.finiteCriticalDepth_le q.isChain_sub_mem (definingParameters_normalized q)
  have hv := simpleCharacters_high_values ψF hψ q hm hθ
  refine ⟨simpleHGroup_eq_unitFiltration_at_high_index q hm, θ, ?_, hv⟩
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨hθ, fun η hη => MonoidHom.ext fun g => Units.ext ?_⟩
  exact (simpleCharacters_high_values ψF hψ q hm hη g).trans (hv g).symm

end

end Langlands.BushnellKutzko
