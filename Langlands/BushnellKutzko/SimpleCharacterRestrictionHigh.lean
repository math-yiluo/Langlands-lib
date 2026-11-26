import Langlands.BushnellKutzko.SimpleCharacterRestrictionStatement
import Langlands.BushnellKutzko.CorestrictionLatticeDual
import Langlands.BushnellKutzko.StratumEquivalenceOrder
import Mathlib.Data.List.ChainOfFn

/-! # High-index groups and trace characters -/

open ValuativeRel

namespace Langlands.BushnellKutzko

noncomputable section

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F]
  {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

variable (L : LatticeChain 𝒪[F] F V) (ψF : AddChar F ℂ)

/-- The identity belongs to the centralizer summand of the simple H lattice. -/
theorem one_mem_simpleHLattice (n : ℤ) (β : A) (tail : List A) :
    (1 : A) ∈ simpleHLattice L n β tail := by
  have h : (1 : A) ∈ centralizerLattice L β 0 := by
    refine ⟨one_mem L.order, ?_⟩
    simp [adjointMap, LinearMap.sub_apply]
  cases tail with
  | nil => exact Submodule.mem_sup_left h
  | cons => exact Submodule.mem_sup_left h

private theorem simpleHLattice_mono_at_high_index (n : ℤ) (k : ℕ)
    (hk : simpleHCutoff n ≤ (k : ℤ)) (β : A) (tail : List A)
    (hdepth : ∀ x ∈ β :: tail, finiteCriticalDepth L n x ≤ n) :
    L.endFiltration k ≤ simpleHLattice L n β tail := by
  induction tail generalizing β with
  | nil =>
    exact (L.endFiltration_antitone hk).trans le_sup_right
  | cons γ rest ih =>
    have hγ : ∀ x ∈ γ :: rest, finiteCriticalDepth L n x ≤ n :=
      fun x hx => hdepth x (List.mem_cons_of_mem β hx)
    have hβ := hdepth β (List.mem_cons_self ..)
    have hcut : simpleHCutoff (finiteCriticalDepth L n β) ≤ (k : ℤ) := by
      unfold simpleHCutoff at hk ⊢
      omega
    exact (le_inf (ih γ hγ) (L.endFiltration_antitone hcut)).trans le_sup_right

/-- Above all the cutoffs of the recursion the character domain is the absolute unit group. -/
theorem simpleHGroup_eq_unitFiltration_of_cutoffs (n : ℤ) (k : ℕ)
    (hk : simpleHCutoff n ≤ (k : ℤ)) (β : A) (tail : List A)
    (hdepth : ∀ x ∈ β :: tail, finiteCriticalDepth L n x ≤ n) :
    simpleHGroup L n β tail k = L.unitFiltration k := by
  refine le_antisymm (simpleHGroup_le_unitFiltration ..) ?_
  intro g hg
  apply Subgroup.subset_closure
  refine ⟨hg, ?_⟩
  simpa using add_mem (simpleHLattice_mono_at_high_index L n k hk β tail hdepth hg.2.2)
    (one_mem_simpleHLattice L n β tail)

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- The trace character is trivial on the first positive endomorphism filtration step. -/
theorem traceCharacter_eq_one_of_mem (hψ : IsBKAdditiveCharacter ψF) {x : A}
    (hx : x ∈ L.endFiltration 1) : traceCharacter ψF x = 1 := by
  obtain ⟨a, ha, he⟩ := L.trace_mem_maximalIdealInField hx
  rw [traceCharacter_apply, ← he]
  exact hψ.1 a ha

private theorem elementCharacter_mul_high (hψ : IsBKAdditiveCharacter ψF) {b : A}
    {s : ℤ} (hb : b ∈ L.endFiltration s) {k : ℕ} (hk : 1 ≤ s + ((k : ℤ) + k))
    {g h : G} (hg : g ∈ L.unitFiltration k) (hh : h ∈ L.unitFiltration k) :
    elementCharacter (traceCharacter ψF) b (g * h) =
      elementCharacter (traceCharacter ψF) b g * elementCharacter (traceCharacter ψF) b h := by
  have hprod : b * (((g : A) - 1) * ((h : A) - 1)) ∈ L.endFiltration 1 :=
    L.endFiltration_antitone hk (L.mul_mem_endFiltration hb (L.mul_mem_endFiltration hg.2.2 hh.2.2))
  simp only [elementCharacter_apply, Units.val_mul]
  rw [show b * ((g : A) * (h : A) - 1) =
      b * ((g : A) - 1) + b * ((h : A) - 1) + b * (((g : A) - 1) * ((h : A) - 1)) by
        noncomm_ring, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
    traceCharacter_eq_one_of_mem L ψF hψ hprod, mul_one]

/-- On any sufficiently deep unit subgroup, the trace formula is an actual character. -/
def elementCharacterHom (hψ : IsBKAdditiveCharacter ψF) {b : A}
    {s : ℤ} (hb : b ∈ L.endFiltration s) {k : ℕ} (hk : 1 ≤ s + ((k : ℤ) + k))
    {H : Subgroup G} (hH : H ≤ L.unitFiltration k) : H →* ℂˣ where
  toFun g := (traceCharacter ψF).toMonoidHom.toHomUnits
    (Multiplicative.ofAdd (b * ((g.val : A) - 1)))
  map_one' := by
    apply Units.ext
    change (traceCharacter ψF) (b * ((1 : A) - 1)) = 1
    simp
  map_mul' g h := by
    apply Units.ext
    exact elementCharacter_mul_high L ψF hψ hb hk (hH g.prop) (hH h.prop)

@[simp]
theorem elementCharacterHom_apply (hψ : IsBKAdditiveCharacter ψF) {b : A}
    {s : ℤ} (hb : b ∈ L.endFiltration s) {k : ℕ} (hk : 1 ≤ s + ((k : ℤ) + k))
    {H : Subgroup G} (hH : H ≤ L.unitFiltration k) (g : H) :
    (elementCharacterHom L ψF hψ hb hk hH g : ℂ) =
      elementCharacter (traceCharacter ψF) b g := rfl

/-- An endomorphism at filtration step `s` has trivial trace character on `U^k` if `s+k≥1`. -/
theorem elementCharacter_eq_one_of_depth (hψ : IsBKAdditiveCharacter ψF) {b : A}
    {s : ℤ} (hb : b ∈ L.endFiltration s) {k : ℕ} (hk : 1 ≤ s + (k : ℤ))
    {g : G} (hg : g ∈ L.unitFiltration k) :
    elementCharacter (traceCharacter ψF) b g = 1 :=
  traceCharacter_eq_one_of_mem L ψF hψ
    (L.endFiltration_antitone hk (L.mul_mem_endFiltration hb hg.2.2))

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem finiteCriticalDepth_of_criticalExponent_eq (n r : ℤ) (β : A)
    (h : criticalExponent L β = ((-r : ℤ) : WithBot ℤ)) :
    finiteCriticalDepth L n β = r := by
  simp [finiteCriticalDepth, simpleCriticalDepth, h]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Every term of a defining sequence has finite critical depth at most the level. -/
theorem Stratum.DefiningSequenceChoice.finiteCriticalDepth_le {S : Stratum 𝒪[F] F V}
    (q : S.DefiningSequenceChoice) :
    ∀ x ∈ S.b :: q.tail, finiteCriticalDepth S.chain S.n x ≤ S.n := by
  obtain ⟨_, hterms, _, _, _, hstep, hlast, _⟩ := q.isDefiningSequence
  have hdepth : ∀ i, finiteCriticalDepth S.chain S.n (q.terms i).b ≤ S.n := by
    apply Fin.lastCases
    · rcases hlast with h | h
      · rw [finiteCriticalDepth_of_criticalExponent_eq _ _ _ _ h]
      · simp [finiteCriticalDepth, simpleCriticalDepth, h]
    · intro i
      rw [finiteCriticalDepth_of_criticalExponent_eq _ _ _ _
        (hstep i).1]
      rw [← (hterms i.succ).2.1]
      exact (q.terms i.succ).r_lt_n.le
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · simpa only [q.firstElement] using hdepth 0
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact hdepth i.succ

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- In the high-index range of BK93 (3.2.4) the domain is the absolute unit group. -/
theorem simpleHGroup_eq_unitFiltration_at_high_index {S : Stratum 𝒪[F] F V}
    (q : S.DefiningSequenceChoice) {m : ℕ} (hm : S.n / 2 ≤ (m : ℤ)) :
    simpleHGroup S.chain S.n S.b q.tail (m + 1) = S.chain.unitFiltration (m + 1) :=
  simpleHGroup_eq_unitFiltration_of_cutoffs S.chain S.n (m + 1) (by
    unfold simpleHCutoff
    omega) S.b q.tail q.finiteCriticalDepth_le

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Consecutive defining elements differ by the endomorphism lattice at the negative critical
depth of the first element. -/
theorem Stratum.DefiningSequenceChoice.isChain_sub_mem {S : Stratum 𝒪[F] F V}
    (q : S.DefiningSequenceChoice) : (S.b :: q.tail).IsChain
      (fun x y => x - y ∈ S.chain.endFiltration (-finiteCriticalDepth S.chain S.n x)) := by
  change (S.b :: List.ofFn fun i : Fin q.steps => (q.terms i.succ).b).IsChain _
  rw [← q.firstElement, ← List.ofFn_succ (f := fun i : Fin (q.steps + 1) => (q.terms i).b)]
  rw [List.isChain_ofFn]
  intro i hi
  let j : Fin q.steps := ⟨i, by omega⟩
  obtain ⟨_, _, _, _, _, hs, _, _⟩ := q.isDefiningSequence
  change (q.terms j.castSucc).b - (q.terms j.succ).b ∈
    S.chain.endFiltration (-finiteCriticalDepth S.chain S.n (q.terms j.castSucc).b)
  rw [finiteCriticalDepth_of_criticalExponent_eq _ _ _ _ (hs j).1]
  simpa only [neg_sub] using (S.chain.endFiltration (-(q.terms j.succ).r)).neg_mem (hs j).2

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem elementCharacter_sub_mul (b c : A) (g : G) :
    elementCharacter (traceCharacter ψF) c g * elementCharacter (traceCharacter ψF) (b - c) g =
      elementCharacter (traceCharacter ψF) b g := by
  simp only [elementCharacter_apply, ← AddChar.map_add_eq_mul]
  congr 1
  noncomm_ring

/-- A simple character at high index has the prescribed trace values. -/
theorem simpleCharacters_high_values_of_cutoffs (hψ : IsBKAdditiveCharacter ψF)
    (n : ℤ) (m : ℕ) (hm : n / 2 ≤ (m : ℤ)) (β : A) (tail : List A)
    (hdepth : ∀ x ∈ β :: tail, finiteCriticalDepth L n x ≤ n)
    (hstep : (β :: tail).IsChain
      (fun x y => x - y ∈ L.endFiltration (-finiteCriticalDepth L n x)))
    {θ : simpleHGroup L n β tail (m + 1) →* ℂˣ}
    (hθ : θ ∈ simpleCharacters ψF L n β tail m) (g : simpleHGroup L n β tail (m + 1)) :
    (θ g : ℂ) = elementCharacter (traceCharacter ψF) β g := by
  have hcut : simpleHCutoff n ≤ ((m + 1 : ℕ) : ℤ) := by unfold simpleHCutoff; omega
  induction tail generalizing β with
  | nil =>
    rw [simpleCharacters] at hθ
    exact hθ.1 g (L.unitFiltration_antitone (by omega : (simpleHCutoff n).toNat ≤ m + 1)
      (simpleHGroup_le_unitFiltration L n β [] (m + 1) g.prop))
  | cons γ rest ih =>
    let r := finiteCriticalDepth L n β
    obtain ⟨hdiff, hrest⟩ := List.isChain_cons_cons.mp hstep
    have hdepth' : ∀ x ∈ γ :: rest, finiteCriticalDepth L n x ≤ n :=
      fun x hx => hdepth x (List.mem_cons_of_mem β hx)
    have hrn : r ≤ n := hdepth β (List.mem_cons_self ..)
    have hmax : max m (r / 2).toNat = m := by
      apply max_eq_left
      omega
    by_cases hmr : (m : ℤ) < finiteCriticalDepth L n β
    · simp only [simpleCharacters, ite_eq_left hmr] at hθ
      rw [hmax] at hθ
      obtain ⟨_, _, θ₀, hθ₀, ha⟩ := hθ
      obtain ⟨_, hg₀, h⟩ := ha g
      rw [h, ih γ hdepth' hrest hθ₀ ⟨g, hg₀⟩]
      exact elementCharacter_sub_mul ψF β γ g
    · simp only [simpleCharacters, ite_eq_right hmr] at hθ
      obtain ⟨θ₀, hθ₀, _, ha⟩ := hθ
      obtain ⟨_, hg₀, h⟩ := ha g
      rw [h, ih γ hdepth' hrest hθ₀ ⟨g, hg₀⟩, mul_one]
      have hmr' : r ≤ (m : ℤ) := le_of_not_gt hmr
      have htriv := elementCharacter_eq_one_of_depth L ψF hψ hdiff
        (by omega : 1 ≤ -r + ((m + 1 : ℕ) : ℤ))
        (simpleHGroup_le_unitFiltration L n β (γ :: rest) (m + 1) g.prop)
      simpa only [htriv, mul_one] using (elementCharacter_sub_mul ψF β γ g)

/-- The high-index uniqueness part of BK93 (3.2.4). -/
theorem simpleCharacters_high_values (hψ : IsBKAdditiveCharacter ψF)
    {S : Stratum 𝒪[F] F V} (q : S.DefiningSequenceChoice) {m : ℕ} (hm : S.n / 2 ≤ (m : ℤ))
    {θ : simpleHGroup S.chain S.n S.b q.tail (m + 1) →* ℂˣ}
    (hθ : θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail m)
    (g : simpleHGroup S.chain S.n S.b q.tail (m + 1)) :
    (θ g : ℂ) = elementCharacter (traceCharacter ψF) S.b g :=
  simpleCharacters_high_values_of_cutoffs S.chain ψF hψ S.n m hm S.b q.tail
    q.finiteCriticalDepth_le q.isChain_sub_mem hθ g

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The trace character of a parameter is invariant under conjugation by its centralizer. -/
theorem elementCharacter_conj_of_centralizer {b : A} {x : G}
    (hx : x ∈ centralizerUnitGroup b) (g : G) :
    elementCharacter (traceCharacter ψF) b (x * g * x⁻¹) =
      elementCharacter (traceCharacter ψF) b g := by
  have hcomm : b * (x : A) = (x : A) * b := hx
  have hsub : ((x * g * x⁻¹ : G) : A) - 1 = (x : A) * ((g : A) - 1) * (↑x⁻¹ : A) := by
    simp only [Units.val_mul, mul_sub, mul_one, sub_mul, Units.mul_inv]
  rw [elementCharacter_apply, elementCharacter_apply, hsub, traceCharacter_apply,
    traceCharacter_apply]
  congr 1
  calc
    LinearMap.trace F V (b * ((x : A) * ((g : A) - 1) * (↑x⁻¹ : A))) =
        LinearMap.trace F V ((x : A) * (b * ((g : A) - 1)) * (↑x⁻¹ : A)) := by
          simp only [← mul_assoc, hcomm]
    _ = LinearMap.trace F V (b * ((g : A) - 1)) := LinearMap.trace_conj F _ _

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- On a normalized subgroup, the trace formula gives a character normalized by the
centralizer elements that preserve the subgroup. -/
theorem characterNormalizer_of_trace_values {b : A} {H K : Subgroup G}
    (hK : K ≤ centralizerUnitGroup b) (hnorm : K ≤ Subgroup.normalizer (H : Set G))
    {θ : H →* ℂˣ} (hθ : ∀ g : H, (θ g : ℂ) = elementCharacter (traceCharacter ψF) b g) :
    (K : Set G) ⊆ characterNormalizer θ := by
  intro x hx
  refine ⟨hnorm hx, fun g hg => Units.ext ?_⟩
  rw [hθ, hθ]
  exact elementCharacter_conj_of_centralizer ψF (hK hx) g

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The finite critical depth of a terminal defining element is the common level. -/
theorem Stratum.DefiningSequenceChoice.finiteCriticalDepth_of_tail_nil {S : Stratum 𝒪[F] F V}
    (q : S.DefiningSequenceChoice) (hq : q.tail = []) :
    finiteCriticalDepth S.chain S.n S.b = S.n := by
  have hz : q.steps = 0 := by
    simpa [Stratum.DefiningSequenceChoice.tail] using congrArg List.length hq
  have hi : Fin.last q.steps = (0 : Fin (q.steps + 1)) := Fin.ext (by simpa using hz)
  obtain ⟨_, _, _, _, _, _, hlast, _⟩ := q.isDefiningSequence
  rw [hi, q.firstElement] at hlast
  rcases hlast with h | h
  · exact finiteCriticalDepth_of_criticalExponent_eq _ _ _ _ h
  · simp [finiteCriticalDepth, simpleCriticalDepth, h]

end

end Langlands.BushnellKutzko
