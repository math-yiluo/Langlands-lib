import Langlands.BushnellKutzko.SimpleCharacterCommutatorStep
import Langlands.BushnellKutzko.SimpleCharacterTransferIntersection

/-! # Passing from a successor character to the preceding character -/

noncomputable section

open ValuativeRel
open scoped Pointwise commutatorElement Classical

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {V : Type uV} [AddCommGroup V] [Module F V]

local notation "O" => 𝒪[F]
local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem finiteCriticalDepth_of_negNat (L : LatticeChain O F V) (n : ℤ) (b : A) (r : ℕ)
    (hr : criticalExponent L b = ((-(r : ℤ) : ℤ) : WithBot ℤ)) : finiteCriticalDepth L n b = r := by
  rw [finiteCriticalDepth, simpleCriticalDepth, hr]
  change -(-(r : ℤ)) = (r : ℤ)
  simp

/-- At an index below the finite critical depth, the character factors
through the relative determinant on the relative domain and is invariant
under the relative order normalizer. -/
theorem character_determinant_normalizer_finite (L : LatticeChain O F V) (n : ℤ)
    (ψF : AddChar F ℂ) (b : A) (tail : List A) (m : ℕ) (hm : (m : ℤ) < finiteCriticalDepth L n b)
    {θ : simpleHGroup L n b tail (m + 1) →* ℂˣ} (hθ : θ ∈ simpleCharacters ψF L n b tail m) :
    factorsThroughCentralizerDet b θ ∧ relativeOrderNormalizer L b ≤ characterNormalizerSubgroup θ := by
  cases tail with
  | nil => exact ⟨hθ.2, relativeOrderNormalizer_le_characterNormalizerSubgroup_nil L n ψF b m hθ⟩
  | cons c tail =>
    simp only [simpleCharacters, ite_eq_left hm] at hθ
    exact ⟨hθ.1, hθ.2.1⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem exists_mul_relative_mixed (L : LatticeChain O F V) (c : A) {k d : ℕ} {j : ℤ}
    (hk : 1 ≤ k) {x : G}
    (hx : (x : A) - 1 ∈ centralizerLattice L c k ⊔ mixedAdjointLattice L c d j) :
    ∃ u ∈ relativeUnitFiltration L c k, ∃ v : G, (v : A) - 1 ∈ mixedAdjointLattice L c d j ∧ u * v = x := by
  have hQ : centralizerLattice L c k ≤ L.endFiltration 1 := fun _ h =>
    L.endFiltration_antitone (by exact_mod_cast hk) h.1
  have hQM : centralizerLattice L c k * mixedAdjointLattice L c d j ≤ mixedAdjointLattice L c d j := by
    apply Submodule.mul_le.mpr
    intro u hu v hv
    have hu' := L.endFiltration_antitone (Int.natCast_nonneg k) hu.1
    constructor
    · change u * v ∈ L.endFiltration d
      simpa only [zero_add] using L.mul_mem_endFiltration hu' hv.1
    · change adjointMap F c (u * v) ∈ L.endFiltration (d + j)
      rw [adjointMap_mul_left_of_ker c (show adjointMap F c u = 0 from hu.2)]
      have hv' : adjointMap F c v ∈ L.endFiltration (d + j) := hv.2
      simpa only [zero_add] using L.mul_mem_endFiltration hu' hv'
  have hInv (u : G) (hu : (u : A) - 1 ∈ centralizerLattice L c k) :
      (↑u⁻¹ : A) - 1 ∈ centralizerLattice L c k :=
    (mem_relativeUnitFiltration_iff_of_pos L c hk u⁻¹).mp
      ((relativeUnitFiltration L c k).inv_mem ((mem_relativeUnitFiltration_iff_of_pos L c hk u).mpr hu))
  obtain ⟨u, hu, v, hv, huv⟩ := exists_mul_of_sub_one_mem_sup L hQ hQM hInv hx
  exact ⟨u, (mem_relativeUnitFiltration_iff_of_pos L c hk u).mpr hu, v, hv, huv⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem characterCommutatorFormula_scalar_nil (L : LatticeChain O F V)
    (n : ℤ) (ψF : AddChar F ℂ) {b : A} (hb : elementAlgebra b = ⊥) (m : ℕ)
    {θ : simpleHGroup L n b [] (m + 1) →* ℂˣ} (hθ : θ ∈ simpleCharacters ψF L n b [] m)
    {k l : ℕ} (hkl : m + 1 ≤ k + l) {x y : G}
    (hx : x ∈ L.unitFiltration k) (hy : y ∈ L.unitFiltration l) :
    characterCommutatorFormula ψF b θ x y := by
  have hb' : b ∈ (⊥ : Subalgebra F A) := hb ▸ Algebra.self_mem_adjoin_singleton F b
  obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hb'
  have hc (u : G) : u ∈ centralizerUnitGroup b := by
    change Commute b (u : A)
    rw [← ha]
    exact Algebra.commutes a _
  exact relative_commutator_formula L ψF b θ hθ.2 (relativeUnitFiltration_le_simpleHGroup L n b [] _)
    hkl ⟨hc x, hx⟩ ⟨hc y, hy⟩

/-- The terminal calculation provides both versions of the commutator formula. -/
theorem simpleCharacterCommutatorAt_nil (L : LatticeChain O F V) (ψF : AddChar F ℂ)
    (hψ : IsBKAdditiveCharacter ψF) (b : A) {r m : ℕ} (hm : r / 2 ≤ m)
    (hb : b ∈ L.endFiltration (-(r : ℤ)))
    {θ : simpleHGroup L r b [] (m + 1) →* ℂˣ} (hθ : θ ∈ simpleCharacters ψF L r b [] m) :
    SimpleCharacterCommutatorAt L ψF b (simpleJGroup L r b []) r m θ := by
  have eval {k l : ℕ} (hkl : m + 1 ≤ k + l) (htrace : r + 1 ≤ k + 2 * l) {x y : G}
      (hx : x ∈ L.unitFiltration k) (hy : y ∈ L.unitFiltration l) :
      characterCommutatorFormula ψF b θ x y := by
    apply characterCommutatorFormula_of_terminal L r ψF hψ hb hθ _ _ hx hy
    · unfold simpleHCutoff
      omega
    · exact_mod_cast htrace
  constructor
  · intro k l hk hl hkl htrace x y hx hy
    exact eval hkl htrace ((L.mem_unitFiltration_of_sub_one_iff hk).mpr hx.1)
      ((L.mem_unitFiltration_of_sub_one_iff hl).mpr hy.1)
  · intro k l hk _ hkl htrace x y hx hy
    exact eval hkl htrace ((L.mem_unitFiltration_of_sub_one_iff hk).mpr hx.1)
      (simpleJGroup_le_unitFiltration L r b [] l hy)

/-- The nonterminal calculation, with the higher-layer equalities and the
relative factorization of mixed and J inputs supplied. -/
theorem simpleCharacterCommutatorAt_cons (L : LatticeChain O F V) (n : ℤ)
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF) (b c : A) (tail : List A)
    {r m : ℕ} (hcrit : criticalExponent L b = ((-(r : ℤ) : ℤ) : WithBot ℤ))
    (hm : r / 2 ≤ m) (hmr : m < r) (hδ : b - c ∈ L.endFiltration (-(r : ℤ)))
    (hH : simpleHGroup L n b (c :: tail) (m + 1) = simpleHGroup L n c tail (m + 1))
    (hJ : ∀ l : ℕ, (r + 1) / 2 ≤ l → simpleJGroup L n b (c :: tail) l = simpleJGroup L n c tail l)
    (hJb : ∀ {l : ℕ} {y : G}, 1 ≤ l → y ∈ simpleJGroup L n b (c :: tail) l →
      ∃ u ∈ relativeUnitFiltration L b l, ∃ v ∈ simpleJGroup L n b (c :: tail) (max l ((r + 1) / 2)), u * v = y)
    (hnext : (elementAlgebra c = ⊥ ∧ tail = []) ∨ ∃ s : ℕ,
      r < s ∧ criticalExponent L c = ((-(s : ℤ) : ℤ) : WithBot ℤ) ∧
      (∀ k : ℕ, mixedAdjointLattice L b k (-(r : ℤ)) = centralizerLattice L c k ⊔
        mixedAdjointLattice L c (k + (s - r) : ℕ) (-(s : ℤ))) ∧
      (∀ {l : ℕ} {y : G}, 1 ≤ l → y ∈ simpleJGroup L n c tail l →
        ∃ u ∈ relativeUnitFiltration L c l, ∃ v ∈ simpleJGroup L n c tail (max l ((s + 1) / 2)), u * v = y) ∧
      (∀ θ₀ ∈ simpleCharacters ψF L n c tail m,
        let inc := simpleHGroup_antitone L n c tail (Nat.succ_le_succ (le_max_left m (s / 2)))
        SimpleCharacterCommutatorAt L ψF c (simpleJGroup L n c tail) s (max m (s / 2))
          (θ₀.comp (Subgroup.inclusion inc))))
    {θ : simpleHGroup L n b (c :: tail) (m + 1) →* ℂˣ}
    (hθ : θ ∈ simpleCharacters ψF L n b (c :: tail) m) :
    SimpleCharacterCommutatorAt L ψF b (simpleJGroup L n b (c :: tail)) r m θ := by
  have hf := finiteCriticalDepth_of_negNat L n b r hcrit
  have hmf : (m : ℤ) < finiteCriticalDepth L n b := hf.symm ▸ (by exact_mod_cast hmr : (m : ℤ) < r)
  have hfhalf : (finiteCriticalDepth L n b / 2).toNat = r / 2 := by rw [hf]; omega
  have hθ' := hθ
  simp only [simpleCharacters, ite_eq_left hmf, Set.mem_ofPred_eq] at hθ'
  rw [hfhalf, max_eq_left hm] at hθ'
  obtain ⟨_, hθnorm, θ₀, hθ₀, hagree⟩ := hθ'
  let θ₀' := θ₀.comp (Subgroup.inclusion hH.le)
  have htwist (u : simpleHGroup L n b (c :: tail) (m + 1)) :
      (θ u : ℂ) = (θ₀' u : ℂ) * elementCharacter (traceCharacter ψF) (b - c) (u : G) := by
    obtain ⟨_, _, hv⟩ := hagree u
    exact hv
  have eval {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hkl : m + 1 ≤ k + l) (ht : r + 1 ≤ k + 2 * l)
      {x y : G} (hx : (x : A) - 1 ∈ mixedAdjointLattice L b k (-(r : ℤ)))
      (hy : (y : A) - 1 ∈ mixedAdjointLattice L b l (-(r : ℤ)) ∨
        (r + 1) / 2 ≤ l ∧ y ∈ simpleJGroup L n b (c :: tail) l) :
      characterCommutatorFormula ψF b θ x y := by
    have hxU := (L.mem_unitFiltration_of_sub_one_iff hk).mpr hx.1
    have hyU : y ∈ L.unitFiltration l := by
      rcases hy with h | ⟨_, h⟩
      · exact (L.mem_unitFiltration_of_sub_one_iff hl).mpr h.1
      · exact simpleJGroup_le_unitFiltration L n b (c :: tail) l h
    have hc : characterCommutatorFormula ψF c θ₀ x y := by
      rcases hnext with ⟨hscalar, htail⟩ | ⟨s, hrs, hs, hMixed, hJc, ih⟩
      · subst tail
        exact characterCommutatorFormula_scalar_nil L n ψF hscalar m hθ₀ hkl hxU hyU
      · have hmf' : (m : ℤ) < finiteCriticalDepth L n c := by
          rw [finiteCriticalDepth_of_negNat L n c s hs]
          omega
        obtain ⟨hdet, hnorm⟩ := character_determinant_normalizer_finite L n ψF c tail m hmf' hθ₀
        have hrel := relativeUnitFiltration_le_simpleHGroup L n c tail (m + 1)
        obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := exists_mul_relative_mixed L c hk ((hMixed k) ▸ hx)
        have ih₀ := ih θ₀ hθ₀
        rcases hy with hy | ⟨hlr, hy⟩
        · obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := exists_mul_relative_mixed L c hl ((hMixed l) ▸ hy)
          have hlow : (↑(y₁ * y₂) : A) - 1 ∈ mixedAdjointLattice L c l (-(s : ℤ)) := by
            rw [hMixed] at hy
            apply (sup_le (centralizerLattice_le_mixedAdjointLattice L c l (-(s : ℤ))) ?_) hy
            intro z hz
            exact ⟨L.endFiltration_antitone (by omega) hz.1, L.endFiltration_antitone (by omega) hz.2⟩
          exact simpleCharacterCommutatorAt_successor_mixed L ψF c _ hrs hm hk hl hkl ht _ θ₀ hdet hnorm hrel
            ih₀ hx₁ hx₂ hy₁ hy₂ hlow
        · rw [hJ l hlr] at hy
          obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := hJc hl hy
          exact simpleCharacterCommutatorAt_successor_J L ψF c _ hrs hm hk hl hkl ht le_rfl _ θ₀ hdet hnorm hrel
            ih₀ hx₁ hx₂ hy₁ hy₂ hy
    obtain ⟨hcc, hcval⟩ := hc
    have hbefore : characterCommutatorFormula ψF c θ₀' x y := ⟨hH.ge hcc, hcval⟩
    have helem := elementCharacter_commutator_of_depth L ψF hψ hδ (by exact_mod_cast ht) hxU hyU
    have h := characterCommutatorFormula.of_twist ψF hbefore htwist helem
    simpa only [add_sub_cancel] using h
  constructor
  · intro k l hk hl hkl ht x y hx hy
    exact eval hk hl hkl ht hx (Or.inl hy)
  · intro k l hk hl hkl ht x y hx hy
    rcases le_or_gt ((r + 1) / 2) l with h | h
    · exact eval hk hl hkl ht hx (Or.inr ⟨h, hy⟩)
    · let d := (r + 1) / 2
      have hd : max l ((r + 1) / 2) = d := max_eq_right h.le
      obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := hJb hl hy
      rw [hd] at hy₂
      have h₁ := eval hk hl hkl ht hx
        (Or.inl (relativeUnitFiltration_sub_one_mem_mixed L b hl (-(r : ℤ)) hy₁))
      have h₂ := eval hk (show 1 ≤ d by omega) (show m + 1 ≤ k + d by omega)
        (show r + 1 ≤ k + 2 * d by omega) hx (Or.inr ⟨le_rfl, hy₂⟩)
      refine characterCommutatorFormula.mul_right ψF h₁ h₂
        (hθnorm (relativeUnitFiltration_le_relativeOrderNormalizer L b l hy₁)) ?_
      have hb := conjugation_sub_mem_of_mem_mixedAdjointUnitGroup
        (show x ∈ mixedAdjointUnitGroup L b k (-(r : ℤ)) hk from hx)
      have hmem := L.mul_mem_endFiltration hb (L.mul_mem_endFiltration hy₁.2.2.2
        (simpleJGroup_le_unitFiltration L n b (c :: tail) d hy₂).2.2)
      have hbound : (1 : ℤ) ≤ (k : ℤ) + (-(r : ℤ)) + ((l : ℤ) + (d : ℤ)) := by
        dsimp only [d]
        omega
      obtain ⟨a, ha, he⟩ := L.trace_mem_maximalIdealInField (L.endFiltration_antitone hbound hmem)
      rw [traceCharacter_apply, ← he]
      exact hψ.1 a ha

end Langlands.BushnellKutzko
