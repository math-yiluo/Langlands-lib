import Langlands.Representation.Conductor.PrincipalCongruenceBasisStatement

/-!
# Entrywise principal congruence and positive-level cofinality: proofs

The two-sided entry criterion for the existing principal congruence subgroup,
and cofinality of the positive principal levels among identity neighborhoods
of the actual general linear group over a nonarchimedean local field.
-/

open Matrix Filter Topology

namespace Langlands.Conductor

universe u

section Entry

variable {k : Type u} [Field k]

/-- Identity-matrix entries commute with the inclusion of a subring. -/
theorem subring_coe_one_apply (O : Subring k) (n : ℕ) (i j : Fin (n + 1)) :
    (((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) O) i j : O) : k) =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j := by
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

/-- Identity-matrix entries over a field lie in every subring. -/
theorem one_apply_mem_subring (O : Subring k) (n : ℕ) (i j : Fin (n + 1)) :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j ∈ O := by
  rw [← subring_coe_one_apply O n i j]
  exact Subtype.property _

/-- Membership in the field principal congruence subgroup is the identity
congruence of both the matrix entries and the inverse-matrix entries. -/
theorem mem_principalCongruenceSubgroup_iff (O : Subring k) (n : ℕ) (I : Ideal O)
    (g : GeneralLinearGroup (Fin (n + 1)) k) :
    g ∈ principalCongruenceSubgroup O n I ↔
      (∀ i j : Fin (n + 1), ∃ x : O, x ∈ I ∧
        (x : k) = g i j - (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j) ∧
      (∀ i j : Fin (n + 1), ∃ x : O, x ∈ I ∧
        (x : k) = g⁻¹ i j - (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j) := by
  -- Entries of an included integral matrix, minus the identity, come from `O`.
  have hcoe : ∀ (h : GeneralLinearGroup (Fin (n + 1)) O) (i j : Fin (n + 1)),
      ((h i j - (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) O) i j : O) : k) =
        GeneralLinearGroup.map O.subtype h i j -
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j := by
    intro h i j
    rw [GeneralLinearGroup.map_apply, AddSubgroupClass.coe_sub, subring_coe_one_apply]
    rfl
  constructor
  · rintro ⟨h, hh, rfl⟩
    have hhi : h⁻¹ ∈ integralPrincipalCongruence n I := inv_mem hh
    refine ⟨fun i j => ⟨_, (mem_integralPrincipalCongruence n I h).1 hh i j, hcoe h i j⟩,
      fun i j => ⟨_, (mem_integralPrincipalCongruence n I h⁻¹).1 hhi i j, ?_⟩⟩
    rw [hcoe h⁻¹ i j, map_inv]
  · rintro ⟨hg, hgi⟩
    -- Both conditions make `g` integral, so it comes from `GL_(n+1)(O)`.
    have hmem : ∀ (x : O) (y : k) (i j : Fin (n + 1)),
        (x : k) = y - (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j → y ∈ O := by
      intro x y i j hx
      rw [← sub_add_cancel y ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j), ← hx]
      exact add_mem x.property (one_apply_mem_subring O n i j)
    have hint : g ∈ integralSubgroup O n := (mem_integralSubgroup O n g).2
      ⟨fun i j => (hg i j).elim fun x hx => hmem x _ i j hx.2,
        fun i j => (hgi i j).elim fun x hx => hmem x _ i j hx.2⟩
    obtain ⟨h, rfl⟩ := hint
    refine (map_mem_principalCongruenceSubgroup O n I h).2
      ((mem_integralPrincipalCongruence n I h).2 fun i j => ?_)
    obtain ⟨x, hxI, hx⟩ := hg i j
    have hxe : x = h i j - (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) O) i j :=
      Subtype.val_injective (hx.trans (hcoe h i j).symm)
    exact hxe ▸ hxI

/-- The entry component of the published basis statement. -/
theorem principalCongruenceEntry :
    PrincipalCongruenceEntryStatement.{u} :=
  fun _ _ O n I g => mem_principalCongruenceSubgroup_iff O n I g

end Entry

section Cofinal

variable (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

/-- The open subgroup has the principal level subgroup as its underlying set. -/
theorem coe_principalLevelOpenSubgroup (n a : ℕ) :
    (principalLevelOpenSubgroup k n a : Set (GeneralLinearGroup (Fin (n + 1)) k)) =
      principalLevelSubgroup k n a :=
  rfl

/-- The positive principal levels intersect in the identity. -/
theorem eq_one_of_forall_mem_principalLevelSubgroup (n : ℕ)
    {g : GeneralLinearGroup (Fin (n + 1)) k}
    (hg : ∀ a : ℕ, g ∈ principalLevelSubgroup k n (a + 1)) : g = 1 := by
  obtain ⟨h, -, rfl⟩ := hg 0
  have hker : ∀ a : ℕ, h ∈ integralPrincipalCongruence n
      (IsLocalRing.maximalIdeal (ValuativeRel.valuation k).integer ^ (a + 1)) :=
    fun a => (map_mem_principalCongruenceSubgroup _ n _ h).1 (hg a)
  suffices h1 : h = 1 by rw [h1, map_one]
  apply GeneralLinearGroup.ext
  intro i j
  have hmem : h i j - (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) _) i j ∈
      ⨅ a : ℕ, IsLocalRing.maximalIdeal (ValuativeRel.valuation k).integer ^ a := by
    rw [Ideal.mem_iInf]
    intro a
    cases a with
    | zero => simp
    | succ a => exact (mem_integralPrincipalCongruence n _ h).1 (hker a) i j
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top,
    Ideal.mem_bot, sub_eq_zero] at hmem
  rw [GeneralLinearGroup.coe_one]
  exact hmem

/-- Every identity neighborhood of the actual general linear group contains
a positive principal level. -/
theorem exists_pos_principalLevelOpenSubgroup_subset (n : ℕ)
    {U : Set (GeneralLinearGroup (Fin (n + 1)) k)}
    (hU : U ∈ 𝓝 (1 : GeneralLinearGroup (Fin (n + 1)) k)) :
    ∃ a : ℕ, 0 < a ∧
      (principalLevelOpenSubgroup k n a : Set (GeneralLinearGroup (Fin (n + 1)) k)) ⊆ U := by
  obtain ⟨W, hWU, hWo, hW1⟩ := mem_nhds_iff.1 hU
  by_contra hne
  push Not at hne
  -- The positive levels outside `W` form a decreasing sequence of compact closed sets.
  let P : ℕ → Set (GeneralLinearGroup (Fin (n + 1)) k) := fun a =>
    (principalLevelOpenSubgroup k n (a + 1) : Set (GeneralLinearGroup (Fin (n + 1)) k)) ∩ Wᶜ
  have hmono : ∀ a, P (a + 1) ⊆ P a := fun a =>
    Set.inter_subset_inter_left _
      (principalLevelSubgroup_antitone k n (Nat.le_succ (a + 1)))
  have hnonempty : ∀ a, (P a).Nonempty := by
    intro a
    obtain ⟨g, hg, hgU⟩ := Set.not_subset.1 (hne (a + 1) a.succ_pos)
    exact ⟨g, hg, fun hgW => hgU (hWU hgW)⟩
  have hclosed : ∀ a, IsClosed (P a) := fun a =>
    (OpenSubgroup.isClosed _).inter hWo.isClosed_compl
  have hcompact : IsCompact (P 0) :=
    (isCompact_principalLevelOpenSubgroup k n 1).inter_right hWo.isClosed_compl
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    P hmono hnonempty hcompact hclosed
  rw [Set.mem_iInter] at hg
  have hg1 : g = 1 := eq_one_of_forall_mem_principalLevelSubgroup k n fun a => (hg a).1
  exact (hg 0).2 (hg1 ▸ hW1)

/-- The cofinality component of the published basis statement. -/
theorem principalLevelCofinal :
    PrincipalLevelCofinalStatement.{u} :=
  fun k _ _ _ _ n _ hU => exists_pos_principalLevelOpenSubgroup_subset k n hU

end Cofinal

/-- The published two-sided entry criterion and positive-level cofinality. -/
theorem principalCongruenceBasis :
    PrincipalCongruenceBasisStatement.{u} :=
  ⟨principalCongruenceEntry, principalLevelCofinal⟩

end Langlands.Conductor
