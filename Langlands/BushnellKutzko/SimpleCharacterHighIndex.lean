import Langlands.BushnellKutzko.AdditiveDualityProof
import Langlands.BushnellKutzko.SimpleCharacters

/-! # Simple characters at depths at least half the stratum level -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F]
  {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

private def approximationStep (L : LatticeChain 𝒪[F] F V) (n : ℤ) (β γ : A) : Prop :=
  let r := finiteCriticalDepth L n β
  r < n ∧ β - γ ∈ L.endFiltration (-r)

private theorem definingSequence_isChain {S : Stratum 𝒪[F] F V}
    (q : S.DefiningSequenceChoice) :
    (S.b :: q.tail).IsChain (approximationStep S.chain S.n) := by
  have hlist : S.b :: q.tail = List.ofFn (fun i => (q.terms i).b) := by
    rw [List.ofFn_succ, q.firstElement, Stratum.DefiningSequenceChoice.tail]
  rw [hlist, List.isChain_ofFn]
  intro i hi
  let j : Fin q.steps := ⟨i, by omega⟩
  change approximationStep S.chain S.n (q.terms j.castSucc).b (q.terms j.succ).b
  have hlevels := q.isDefiningSequence.2.1 j.succ
  obtain ⟨hcrit, hsub⟩ := q.isDefiningSequence.2.2.2.2.2.1 j
  have hr : finiteCriticalDepth S.chain S.n (q.terms j.castSucc).b = (q.terms j.succ).r := by
    simp [finiteCriticalDepth, simpleCriticalDepth, hcrit]
  unfold approximationStep
  dsimp only
  rw [hr]
  refine ⟨hlevels.2.1 ▸ (q.terms j.succ).r_lt_n, ?_⟩
  convert neg_mem hsub using 1
  abel

private theorem endFiltration_le_simpleHLattice (L : LatticeChain 𝒪[F] F V) (n : ℤ)
    (β : A) (tail : List A) (h : (β :: tail).IsChain (approximationStep L n)) :
    L.endFiltration (simpleHCutoff n) ≤ simpleHLattice L n β tail := by
  induction tail generalizing β with
  | nil => exact le_sup_right
  | cons γ tail ih =>
    obtain ⟨hstep, htail⟩ := List.isChain_cons_cons.mp h
    change _ ≤ centralizerLattice L β 0 ⊔
      (simpleHLattice L n γ tail ⊓ L.endFiltration (simpleHCutoff (finiteCriticalDepth L n β)))
    exact (le_inf (ih γ htail) (L.endFiltration_antitone
      (by have := hstep.1; unfold simpleHCutoff; omega))).trans le_sup_right

private theorem one_mem_simpleHLattice (L : LatticeChain 𝒪[F] F V) (n : ℤ) (β : A)
    (tail : List A) : 1 ∈ simpleHLattice L n β tail := by
  have h₁ : (1 : A) ∈ centralizerLattice L β 0 :=
    ⟨L.mem_order_iff_mem_endFiltration.mp (one_mem L.order), by
      simp [adjointMap]⟩
  cases tail <;> exact Submodule.mem_sup_left h₁

private theorem simpleHGroup_eq_unitFiltration_of_isChain (L : LatticeChain 𝒪[F] F V) (n : ℤ)
    (β : A) (tail : List A) (h : (β :: tail).IsChain (approximationStep L n))
    (m : ℕ) (hm : n / 2 ≤ (m : ℤ)) :
    simpleHGroup L n β tail (m + 1) = L.unitFiltration (m + 1) := by
  apply le_antisymm (simpleHGroup_le_unitFiltration L n β tail _)
  intro g hg
  have hx : (g : A) - 1 ∈ simpleHLattice L n β tail :=
    endFiltration_le_simpleHLattice L n β tail h
      (L.endFiltration_antitone (by unfold simpleHCutoff; omega) hg.2.2)
  exact Subgroup.subset_closure ⟨hg, by
    simpa using add_mem hx (one_mem_simpleHLattice L n β tail)⟩

/-- At depth `m ≥ ⌊n/2⌋`, the domain of simple characters is the entire unit filtration step. -/
theorem simpleHGroup_eq_unitFiltration_of_half_le {S : Stratum 𝒪[F] F V}
    (q : S.DefiningSequenceChoice) (m : ℕ) (hm : S.n / 2 ≤ (m : ℤ)) :
    simpleHGroup S.chain S.n S.b q.tail (m + 1) = S.chain.unitFiltration (m + 1) :=
  simpleHGroup_eq_unitFiltration_of_isChain S.chain S.n S.b q.tail
    (definingSequence_isChain q) m hm

omit [ValuativeRel F] in
private theorem elementCharacter_mul_sub (ψ : AddChar A ℂ) (β γ : A) (g : G) :
    elementCharacter ψ γ g * elementCharacter ψ (β - γ) g = elementCharacter ψ β g := by
  simp only [elementCharacter_apply, ← AddChar.map_add_eq_mul, ← add_mul,
    show γ + (β - γ) = β by abel]

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

private theorem elementCharacter_eq_one_of_mem (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    (L : LatticeChain 𝒪[F] F V) (m : ℕ) {b : A}
    (hb : b ∈ L.endFiltration (-(m : ℤ))) {g : G} (hg : g ∈ L.unitFiltration (m + 1)) :
    elementCharacter (traceCharacter ψF) b g = 1 := by
  have hdual := (additiveDuality F V L ψF hψ.1 hψ.2).1 ((m : ℤ) + 1)
  have hb' : b ∈ additiveDual (traceCharacter ψF) (L.endFiltration ((m : ℤ) + 1) : Set A) := by
    rw [hdual, show (1 : ℤ) - (m + 1) = -m by omega]
    exact hb
  exact hb' ((g : A) - 1) (by exact hg.2.2)

private theorem simpleCharacter_apply_of_isChain (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    (L : LatticeChain 𝒪[F] F V) (n : ℤ) (β : A) (tail : List A)
    (h : (β :: tail).IsChain (approximationStep L n)) (m : ℕ) (hm : n / 2 ≤ (m : ℤ))
    {θ : simpleHGroup L n β tail (m + 1) →* ℂˣ} (hθ : θ ∈ simpleCharacters ψF L n β tail m)
    (g : simpleHGroup L n β tail (m + 1)) :
    (θ g : ℂ) = elementCharacter (traceCharacter ψF) β g := by
  induction tail generalizing β with
  | nil =>
    exact hθ.1 g (L.unitFiltration_antitone (by unfold simpleHCutoff; omega)
      (simpleHGroup_le_unitFiltration L n β [] _ g.property))
  | cons γ tail ih =>
    obtain ⟨hstep, htail⟩ := List.isChain_cons_cons.mp h
    let r := finiteCriticalDepth L n β
    have hr : r < n := hstep.1
    have hsub : β - γ ∈ L.endFiltration (-r) := hstep.2
    simp only [simpleCharacters] at hθ
    by_cases hmr : (m : ℤ) < r
    · have hj : max m (r / 2).toNat = m := by omega
      rw [ite_eq_left hmr, hj] at hθ
      obtain ⟨_, _, θ₀, hθ₀, hagrees⟩ := hθ
      obtain ⟨_, hg₀, heq⟩ := hagrees g
      exact heq.trans (by
        rw [ih γ htail hθ₀ ⟨g, hg₀⟩]
        exact elementCharacter_mul_sub (traceCharacter ψF) β γ g)
    · rw [ite_eq_right hmr] at hθ
      obtain ⟨θ₀, hθ₀, _, hagrees⟩ := hθ
      obtain ⟨_, hg₀, heq⟩ := hagrees g
      have hdiff : elementCharacter (traceCharacter ψF) (β - γ) g = 1 :=
        elementCharacter_eq_one_of_mem ψF hψ L m (L.endFiltration_antitone (by omega) hsub)
          (simpleHGroup_le_unitFiltration L n β (γ :: tail) _ g.property)
      calc
        (θ g : ℂ) = (θ₀ ⟨g, hg₀⟩ : ℂ) := by simpa only [mul_one] using heq
        _ = elementCharacter (traceCharacter ψF) γ g := ih γ htail hθ₀ ⟨g, hg₀⟩
        _ = elementCharacter (traceCharacter ψF) β g := by
          simpa only [hdiff, mul_one] using elementCharacter_mul_sub (traceCharacter ψF) β γ g

/-- At depth `m ≥ ⌊n/2⌋`, any simple character takes the values of `ψ_β`. -/
theorem simpleCharacter_apply_of_half_le (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    {S : Stratum 𝒪[F] F V} (q : S.DefiningSequenceChoice) (m : ℕ) (hm : S.n / 2 ≤ (m : ℤ))
    {θ : simpleHGroup S.chain S.n S.b q.tail (m + 1) →* ℂˣ}
    (hθ : θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail m)
    (g : simpleHGroup S.chain S.n S.b q.tail (m + 1)) :
    (θ g : ℂ) = elementCharacter (traceCharacter ψF) S.b g :=
  simpleCharacter_apply_of_isChain ψF hψ S.chain S.n S.b q.tail (definingSequence_isChain q)
    m hm hθ g

/-- At depth `m ≥ ⌊n/2⌋`, there is at most one simple character for a defining sequence. -/
theorem simpleCharacters_subsingleton_of_half_le (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    {S : Stratum 𝒪[F] F V} (q : S.DefiningSequenceChoice) (m : ℕ) (hm : S.n / 2 ≤ (m : ℤ)) :
    (simpleCharacters ψF S.chain S.n S.b q.tail m).Subsingleton := by
  intro θ hθ χ hχ
  ext g
  exact (simpleCharacter_apply_of_half_le ψF hψ q m hm hθ g).trans
    (simpleCharacter_apply_of_half_le ψF hψ q m hm hχ g).symm

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem eq_of_transport_inter_nonempty {H H' : Subgroup G} (h : H = H')
    (C : Set (H →* ℂˣ)) (C' : Set (H' →* ℂˣ)) (hC : C.Subsingleton) (hC' : C'.Subsingleton)
    (hcommon : (Eq.ndrec (motive := fun K : Subgroup G => Set (K →* ℂˣ)) C h ∩ C').Nonempty) :
    Eq.ndrec (motive := fun K : Subgroup G => Set (K →* ℂˣ)) C h = C' := by
  cases h
  obtain ⟨θ, hθ, hθ'⟩ := hcommon
  exact (hC.eq_singleton_of_mem hθ).trans (hC'.eq_singleton_of_mem hθ').symm

/-- Coherence of simple character sets in the half-level range of BK93 (3.5.8). -/
theorem simpleCharacterCoherence_of_half_le (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    {S T : Stratum 𝒪[F] F V} (q : S.DefiningSequenceChoice) (q' : T.DefiningSequenceChoice)
    (m : ℕ) (hn : T.n = S.n) (hm : S.n / 2 ≤ (m : ℤ)) :
    let H := simpleHGroup S.chain S.n S.b q.tail (m + 1)
    let H' := simpleHGroup T.chain T.n T.b q'.tail (m + 1)
    let C := simpleCharacters ψF S.chain S.n S.b q.tail m
    let C' := simpleCharacters ψF T.chain T.n T.b q'.tail m
    ∀ h : H = H',
      let C₁ := Eq.ndrec (motive := fun K : Subgroup G => Set (K →* ℂˣ)) C h
      (C₁ ∩ C').Nonempty → C₁ = C' := by
  intro H H' C C' h C₁ hcommon
  exact eq_of_transport_inter_nonempty h C C' (simpleCharacters_subsingleton_of_half_le ψF hψ q m hm)
    (simpleCharacters_subsingleton_of_half_le ψF hψ q' m (hn.symm ▸ hm)) hcommon

/-- The domain and value formulas at or above half the level, for any defining sequence. -/
def SimpleCharacterHighIndexStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (S : Stratum 𝒪[F] F V) (q : S.DefiningSequenceChoice) (m : ℕ), S.n / 2 ≤ (m : ℤ) →
      let H := simpleHGroup S.chain S.n S.b q.tail (m + 1)
      H = S.chain.unitFiltration (m + 1) ∧
        ∀ θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail m, ∀ g : H,
          (θ g : ℂ) = elementCharacter (traceCharacter ψF) S.b g

/-- The high-index domain and value formulas follow from the defining-sequence recursion. -/
theorem simpleCharacterHighIndex : SimpleCharacterHighIndexStatement.{uF, uV} := by
  intro F _ _ _ _ V _ _ ψF hψ S q m hm
  exact ⟨simpleHGroup_eq_unitFiltration_of_half_le q m hm,
    fun _ hθ g => simpleCharacter_apply_of_half_le ψF hψ q m hm hθ g⟩

end Langlands.BushnellKutzko
