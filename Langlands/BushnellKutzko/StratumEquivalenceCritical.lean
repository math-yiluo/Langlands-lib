import Langlands.BushnellKutzko.StratumEquivalenceOrder
import Langlands.BushnellKutzko.AdjointExactnessProof
import Langlands.BushnellKutzko.PureSimpleStratum

/-! # Equivalent simple strata: `𝔅 + 𝔓` and the critical exponent (BK93 (2.1.3)–(2.1.4))

Helper results for `StratumEquivalenceStatement`, parts (i) and (ii) of BK93 (2.1.4),
printed p. 50.
-/

open ValuativeRel

namespace Langlands.BushnellKutzko

namespace StratumEquivalence

universe uF uV

section General

variable {O K V : Type*} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

theorem adjointMap_apply (β x : Module.End K V) : adjointMap O β x = β * x - x * β := by
  simp [adjointMap]

/-- `𝔑_k` depends on the chain only through its filtration. -/
theorem adjointLattice_congr {𝓛₁ 𝓛₂ : LatticeChain O K V}
    (h : 𝓛₁.endFiltration = 𝓛₂.endFiltration) (β : Module.End K V) (k : ℤ) :
    adjointLattice 𝓛₁ β k = adjointLattice 𝓛₂ β k := by
  unfold adjointLattice
  rw [h]

/-- `𝔓^k ∩ B` depends on the chain only through its filtration. -/
theorem centralizerLattice_congr {𝓛₁ 𝓛₂ : LatticeChain O K V}
    (h : 𝓛₁.endFiltration = 𝓛₂.endFiltration) (β : Module.End K V) (k : ℤ) :
    centralizerLattice 𝓛₁ β k = centralizerLattice 𝓛₂ β k := by
  unfold centralizerLattice
  rw [h]

/-- The critical index set depends on the chain only through its filtration. -/
theorem criticalIndexSet_congr {𝓛₁ 𝓛₂ : LatticeChain O K V}
    (h : 𝓛₁.endFiltration = 𝓛₂.endFiltration) (β : Module.End K V) :
    criticalIndexSet 𝓛₁ β = criticalIndexSet 𝓛₂ β := by
  unfold criticalIndexSet
  simp only [adjointLattice_congr h, centralizerLattice_congr h, h]

/-- The critical exponent depends on the chain only through its filtration. -/
theorem criticalExponent_congr {𝓛₁ 𝓛₂ : LatticeChain O K V}
    (h : 𝓛₁.endFiltration = 𝓛₂.endFiltration) (β : Module.End K V) :
    criticalExponent 𝓛₁ β = criticalExponent 𝓛₂ β := by
  unfold criticalExponent
  rw [criticalIndexSet_congr h]

variable (𝓛 : LatticeChain O K V)

/-- BK93 (2.1.3): if `β₁ - β₂ ∈ 𝔓^{-r}` and `m ≤ -r`, then `𝔑_m(β₁) = 𝔑_m(β₂)`. -/
theorem adjointLattice_eq_of_sub_mem {β₁ β₂ : Module.End K V} {r m : ℤ} (hm : m ≤ -r)
    (hsub : β₁ - β₂ ∈ 𝓛.endFiltration (-r)) :
    adjointLattice 𝓛 β₁ m = adjointLattice 𝓛 β₂ m := by
  have key : ∀ x ∈ 𝓛.endFiltration 0,
      adjointMap O β₁ x - adjointMap O β₂ x ∈ 𝓛.endFiltration m := by
    intro x hx
    rw [adjointMap_apply, adjointMap_apply,
      show β₁ * x - x * β₁ - (β₂ * x - x * β₂) = (β₁ - β₂) * x - x * (β₁ - β₂) by noncomm_ring]
    apply 𝓛.endFiltration_antitone hm
    refine sub_mem ?_ ?_
    · simpa using 𝓛.mul_mem_endFiltration hsub hx
    · simpa using 𝓛.mul_mem_endFiltration hx hsub
  ext x
  simp only [adjointLattice, Submodule.mem_inf, Submodule.mem_comap]
  constructor
  · rintro ⟨hx, h1⟩
    refine ⟨hx, ?_⟩
    have := sub_mem h1 (key x hx)
    rwa [sub_sub_cancel] at this
  · rintro ⟨hx, h2⟩
    refine ⟨hx, ?_⟩
    have := add_mem h2 (key x hx)
    rwa [add_sub_cancel] at this

/-- `𝔅 ⊆ 𝔑_m(β)` for every `m`. -/
theorem centralizerLattice_le_adjointLattice (β : Module.End K V) (m : ℤ) :
    centralizerLattice 𝓛 β 0 ≤ adjointLattice 𝓛 β m := by
  intro x hx
  simp only [centralizerLattice, Submodule.mem_inf, LinearMap.mem_ker] at hx
  simp only [adjointLattice, Submodule.mem_inf, Submodule.mem_comap]
  exact ⟨hx.1, by rw [hx.2]; exact zero_mem _⟩

/-- `𝔑_k(β) ⊆ 𝔑_m(β)` for `m ≤ k`. -/
theorem adjointLattice_antitone' (β : Module.End K V) {m k : ℤ} (h : m ≤ k) :
    adjointLattice 𝓛 β k ≤ adjointLattice 𝓛 β m := by
  intro x hx
  simp only [adjointLattice, Submodule.mem_inf, Submodule.mem_comap] at hx ⊢
  exact ⟨hx.1, 𝓛.endFiltration_antitone h hx.2⟩

/-- For a scalar `β`, the centralizer lattice `𝔅` is the whole order. -/
theorem centralizerLattice_zero_of_bot {β : Module.End K V}
    (hβ : Algebra.adjoin K ({β} : Set (Module.End K V)) = ⊥) :
    centralizerLattice 𝓛 β 0 = 𝓛.endFiltration 0 := by
  have hmem : β ∈ (⊥ : Subalgebra K (Module.End K V)) := by
    rw [← hβ]
    exact Algebra.self_mem_adjoin_singleton K β
  obtain ⟨c, rfl⟩ := Algebra.mem_bot.1 hmem
  apply le_antisymm inf_le_left
  intro x hx
  refine ⟨hx, ?_⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, adjointMap_apply, Algebra.commutes, sub_self]

/-- For a scalar `β`, the critical index set is empty. -/
theorem criticalIndexSet_eq_empty_of_bot {β : Module.End K V}
    (hβ : Algebra.adjoin K ({β} : Set (Module.End K V)) = ⊥) :
    criticalIndexSet 𝓛 β = ∅ := by
  ext k
  simp only [criticalIndexSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
  rw [centralizerLattice_zero_of_bot 𝓛 hβ]
  exact inf_le_left.trans le_sup_left

/-- Under `k₀(β) < -r`, with the critical index set bounded above when `β` is not scalar,
`𝔑_k(β) ⊆ 𝔅 + 𝔓` for every `k ≥ -r`. -/
theorem adjointLattice_le_of_criticalExponent_lt {β : Module.End K V} {r : ℤ}
    (hβ : Algebra.adjoin K ({β} : Set (Module.End K V)) = ⊥ ∨
      BddAbove (criticalIndexSet 𝓛 β))
    (hk : criticalExponent 𝓛 β < ((-r : ℤ) : WithBot ℤ)) {k : ℤ} (hrk : -r ≤ k) :
    adjointLattice 𝓛 β k ≤ centralizerLattice 𝓛 β 0 ⊔ 𝓛.endFiltration 1 := by
  by_cases hbot : Algebra.adjoin K ({β} : Set (Module.End K V)) = ⊥
  · have := criticalIndexSet_eq_empty_of_bot 𝓛 hbot
    have hk' : k ∉ criticalIndexSet 𝓛 β := by rw [this]; exact Set.notMem_empty k
    simpa [criticalIndexSet] using hk'
  · have hbdd := hβ.resolve_left hbot
    unfold criticalExponent at hk
    simp only [hbot, ↓reduceIte] at hk
    have hlt : sSup (criticalIndexSet 𝓛 β) < -r := WithBot.coe_lt_coe.mp hk
    have hk' : k ∉ criticalIndexSet 𝓛 β := fun hmem =>
      absurd (le_csSup hbdd hmem) (by omega)
    simpa [criticalIndexSet] using hk'

/-- The core of BK93 (2.1.4)(i)–(ii) for a single chain: if `β₁ - β₂ ∈ 𝔓^{-r}` and both
critical exponents are `< -r` (with nonempty bounded critical index sets for nonscalar
elements), then `𝔅₁ + 𝔓 = 𝔅₂ + 𝔓` and `k₀(β₁) = k₀(β₂)`. -/
theorem sup_eq_and_criticalExponent_eq {β₁ β₂ : Module.End K V} {r : ℤ}
    (hsub : β₁ - β₂ ∈ 𝓛.endFiltration (-r))
    (h₁ : Algebra.adjoin K ({β₁} : Set (Module.End K V)) = ⊥ ∨
      ((criticalIndexSet 𝓛 β₁).Nonempty ∧ BddAbove (criticalIndexSet 𝓛 β₁)))
    (h₂ : Algebra.adjoin K ({β₂} : Set (Module.End K V)) = ⊥ ∨
      ((criticalIndexSet 𝓛 β₂).Nonempty ∧ BddAbove (criticalIndexSet 𝓛 β₂)))
    (hk₁ : criticalExponent 𝓛 β₁ < ((-r : ℤ) : WithBot ℤ))
    (hk₂ : criticalExponent 𝓛 β₂ < ((-r : ℤ) : WithBot ℤ)) :
    centralizerLattice 𝓛 β₁ 0 ⊔ 𝓛.endFiltration 1 =
        centralizerLattice 𝓛 β₂ 0 ⊔ 𝓛.endFiltration 1 ∧
      criticalExponent 𝓛 β₁ = criticalExponent 𝓛 β₂ := by
  have hsub' : β₂ - β₁ ∈ 𝓛.endFiltration (-r) := by
    rw [show β₂ - β₁ = -(β₁ - β₂) by abel]
    exact neg_mem hsub
  have hN : ∀ m ≤ -r, adjointLattice 𝓛 β₁ m = adjointLattice 𝓛 β₂ m :=
    fun m hm => adjointLattice_eq_of_sub_mem 𝓛 hm hsub
  have hle₁ := fun k (hrk : -r ≤ k) =>
    adjointLattice_le_of_criticalExponent_lt (k := k) 𝓛 (h₁.imp_right And.right) hk₁ hrk
  have hle₂ := fun k (hrk : -r ≤ k) =>
    adjointLattice_le_of_criticalExponent_lt (k := k) 𝓛 (h₂.imp_right And.right) hk₂ hrk
  have hsup : centralizerLattice 𝓛 β₁ 0 ⊔ 𝓛.endFiltration 1 =
      centralizerLattice 𝓛 β₂ 0 ⊔ 𝓛.endFiltration 1 := by
    apply le_antisymm
    · refine sup_le ?_ le_sup_right
      calc centralizerLattice 𝓛 β₁ 0 ≤ adjointLattice 𝓛 β₁ (-r) :=
            centralizerLattice_le_adjointLattice 𝓛 β₁ (-r)
        _ = adjointLattice 𝓛 β₂ (-r) := hN (-r) le_rfl
        _ ≤ _ := hle₂ (-r) le_rfl
    · refine sup_le ?_ le_sup_right
      calc centralizerLattice 𝓛 β₂ 0 ≤ adjointLattice 𝓛 β₂ (-r) :=
            centralizerLattice_le_adjointLattice 𝓛 β₂ (-r)
        _ = adjointLattice 𝓛 β₁ (-r) := (hN (-r) le_rfl).symm
        _ ≤ _ := hle₁ (-r) le_rfl
  have hC : criticalIndexSet 𝓛 β₁ = criticalIndexSet 𝓛 β₂ := by
    ext k
    simp only [criticalIndexSet, Set.mem_ofPred_eq]
    rcases le_or_gt k (-r) with hk | hk
    · rw [hN k hk, hsup]
    · simp only [hle₁ k hk.le, hle₂ k hk.le]
  refine ⟨hsup, ?_⟩
  unfold criticalExponent
  by_cases hb₁ : Algebra.adjoin K ({β₁} : Set (Module.End K V)) = ⊥ <;>
    by_cases hb₂ : Algebra.adjoin K ({β₂} : Set (Module.End K V)) = ⊥
  · simp only [hb₁, hb₂, ↓reduceIte]
  · exfalso
    have hne := (h₂.resolve_left hb₂).1
    rw [← hC, criticalIndexSet_eq_empty_of_bot 𝓛 hb₁] at hne
    exact Set.not_nonempty_empty hne
  · exfalso
    have hne := (h₁.resolve_left hb₁).1
    rw [hC, criticalIndexSet_eq_empty_of_bot 𝓛 hb₂] at hne
    exact Set.not_nonempty_empty hne
  · simp only [hb₁, hb₂, ↓reduceIte, hC]

end General

section Local

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

/-- For a pure stratum with nonscalar parameter, the critical index set is nonempty and
bounded above (from `adjointExactness`). -/
theorem criticalIndexSet_nonempty_bddAbove {S : Stratum 𝒪[F] F V} (hS : S.IsPure)
    (hns : Algebra.adjoin F ({S.b} : Set (Module.End F V)) ≠ ⊥) :
    (criticalIndexSet S.chain S.b).Nonempty ∧ BddAbove (criticalIndexSet S.chain S.b) := by
  obtain ⟨⟨hf, hu⟩, -⟩ := hS
  let := hf.toField
  let β : elementAlgebra S.b := ⟨S.b, Algebra.self_mem_adjoin_singleton F S.b⟩
  have hemb : subfieldEmbedding F (elementAlgebra S.b) V β = S.b := by
    ext v
    rfl
  have hadj : Algebra.adjoin F ({β} : Set (elementAlgebra S.b)) = ⊤ := by
    have h := Algebra.adjoin_adjoin_coe_preimage (R := F)
      (s := ({S.b} : Set (Module.End F V)))
    have hpre : (((↑) : elementAlgebra S.b → Module.End F V) ⁻¹'
        ({S.b} : Set (Module.End F V))) = {β} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun hx => Subtype.ext hx, fun hx => by rw [hx]⟩
    rw [hpre] at h
    exact h
  have hnsc : ¬ ∃ a : F, algebraMap F (elementAlgebra S.b) a = β := by
    rintro ⟨a, ha⟩
    apply hns
    have hb : S.b ∈ (⊥ : Subalgebra F (Module.End F V)) := by
      have := congrArg Subtype.val ha
      rw [Subalgebra.coe_algebraMap] at this
      have hb' : algebraMap F (Module.End F V) a = S.b := this
      rw [← hb']
      exact Subalgebra.algebraMap_mem _ a
    exact le_bot_iff.1 (Algebra.adjoin_le (Set.singleton_subset_iff.2 hb))
  have := adjointExactness F V (elementAlgebra S.b) S.chain β hadj hnsc hu
  simp only [hemb] at this
  exact ⟨this.2.1, this.2.2.1⟩

/-- BK93 (2.1.4)(i)–(ii): equivalent simple strata have the same `𝔅 + 𝔓` and the same
critical exponent. -/
theorem sup_eq_and_criticalExponent_eq_of_equivalent {S T : Stratum 𝒪[F] F V}
    (h : S.Equivalent T) (hS : S.IsSimple) (hT : T.IsSimple) :
    centralizerLattice S.chain S.b 0 ⊔ S.chain.endFiltration 1 =
        centralizerLattice T.chain T.b 0 ⊔ T.chain.endFiltration 1 ∧
      criticalExponent S.chain S.b = criticalExponent T.chain T.b := by
  have hP := endFiltration_eq_of_equivalent h
  have hr := r_eq_of_equivalent h
  have hsub := sub_mem_of_equivalent h
  have hfacts : ∀ U : Stratum 𝒪[F] F V, U.IsPure →
      Algebra.adjoin F ({U.b} : Set (Module.End F V)) = ⊥ ∨
        ((criticalIndexSet U.chain U.b).Nonempty ∧ BddAbove (criticalIndexSet U.chain U.b)) := by
    intro U hU
    by_cases hbot : Algebra.adjoin F ({U.b} : Set (Module.End F V)) = ⊥
    · exact Or.inl hbot
    · exact Or.inr (criticalIndexSet_nonempty_bddAbove hU hbot)
  have h₁ := hfacts S hS.1
  have h₂ := hfacts T hT.1
  rw [criticalIndexSet_congr hP] at h₁
  have hk₁ := hS.2
  rw [criticalExponent_congr hP, hr] at hk₁
  have hk₂ := hT.2
  rw [centralizerLattice_congr hP, hP, criticalExponent_congr hP]
  exact sup_eq_and_criticalExponent_eq T.chain hsub h₁ h₂ hk₁ hk₂

end Local

end StratumEquivalence

end Langlands.BushnellKutzko
