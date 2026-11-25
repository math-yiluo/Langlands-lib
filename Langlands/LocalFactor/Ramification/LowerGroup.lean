/-
Adapted from the Anthropic Lean formalisation of Fermat's Last Theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, files
`Definitions/Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup.lean`,
`Definitions/Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupSubgroup.lean`.
Copyright 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: the two files are merged; statements are on the Library's
`Langlands.Ramification.lowerGroup` (of which the FLT `IsLocalRing.lowerRamificationGroup` was an
abbreviation), whose antitonicity, normality and zeroth group `Filtration.lean` already proves;
names follow the Library; the `ValuationSubring` wrappers, the example blocks and the in-file
checks are not kept; no options are set. The paired Markdown file lists the changes.
-/
import Langlands.LocalFactor.Ramification.Filtration
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Lower ramification groups of an action on a local ring

Basic facts about `lowerGroup R G i` (the elements of `G` acting trivially on
`R ⧸ maximalIdeal R ^ (i + 1)`, `Filtration.lean`) for a group acting on a local ring: membership,
the zeroth group as the kernel of the action on the residue field, separatedness, and the lower
groups of a subgroup.
-/

namespace Langlands.Ramification

open scoped Pointwise

section Inertia

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [MulSemiringAction G R]

theorem inertia_mono {I J : Ideal R} (h : I ≤ J) :
    I.inertia G ≤ J.inertia G :=
  AddSubgroup.inertia_mono G (Submodule.toAddSubgroup_mono h)

/-- The inertia group of an ideal stable under the action is normal. -/
theorem inertia_normal_of_forall_smul_eq {I : Ideal R}
    (hI : ∀ g : G, g • I = I) : (I.inertia G).Normal := by
  refine ⟨fun σ hσ τ x => ?_⟩

  have key : τ • (σ • (τ⁻¹ • x) - τ⁻¹ • x) ∈ τ • I :=
    Ideal.smul_mem_pointwise_smul _ _ _ (hσ _)
  simpa [smul_sub, smul_smul, mul_assoc, hI τ] using key

end Inertia

section LocalRing

open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

@[simp]
theorem pointwise_smul_maximalIdeal (g : G) :
    g • maximalIdeal R = maximalIdeal R := by
  refine le_antisymm (le_maximalIdeal_of_isPrime _) ?_
  rw [Ideal.subset_pointwise_smul_iff]
  exact le_maximalIdeal_of_isPrime _

@[simp]
theorem pointwise_smul_maximalIdeal_pow (g : G) (n : ℕ) :
    g • (maximalIdeal R) ^ n = (maximalIdeal R) ^ n := by
  rw [Ideal.pointwise_smul_def, Ideal.map_pow, ← Ideal.pointwise_smul_def,
    pointwise_smul_maximalIdeal]

variable {i : ℕ}

/-- `σ ∈ G_i` exactly when `σ x - x ∈ m ^ (i + 1)` for every `x`. -/
@[simp]
theorem mem_lowerGroup {σ : G} :
    σ ∈ lowerGroup R G i ↔ ∀ x : R, σ • x - x ∈ (maximalIdeal R) ^ (i + 1) :=
  Iff.rfl

/-- The zeroth lower group is the kernel of the action on the residue field. -/
theorem lowerGroup_zero_eq_ker :
    lowerGroup R G 0 =
      MonoidHom.ker (MulSemiringAction.toRingAut G (ResidueField R)) := by
  ext σ
  simp only [mem_lowerGroup, zero_add, pow_one, MonoidHom.mem_ker]
  constructor
  · intro hσ
    ext y
    obtain ⟨r, rfl⟩ := residue_surjective y
    have : residue R (σ • r - r) = 0 := (residue_eq_zero_iff _).mpr (hσ r)
    simpa [sub_eq_zero, ResidueField.residue_smul] using this
  · intro hσ r
    rw [← residue_eq_zero_iff, map_sub, ResidueField.residue_smul, sub_eq_zero]
    exact DFunLike.congr_fun hσ (residue R r)

theorem lowerGroup_le_zero (i : ℕ) :
    lowerGroup R G i ≤ lowerGroup R G 0 :=
  (lowerGroup_antitone _ _) (Nat.zero_le i)

theorem iInf_lowerGroup_le_ker_toRingAut
    (hsep : ⨅ n, (maximalIdeal R) ^ n = ⊥) :
    ⨅ i, lowerGroup R G i ≤
      MonoidHom.ker (MulSemiringAction.toRingAut G R) := by
  intro σ hσ
  simp only [Subgroup.mem_iInf, mem_lowerGroup] at hσ
  ext x
  have : σ • x - x ∈ ⨅ n, (maximalIdeal R) ^ n := by
    simp only [Ideal.mem_iInf]
    intro n
    rcases n with _ | n
    · simp
    · exact hσ n x
  rw [hsep] at this
  simpa [sub_eq_zero] using this

/-- If the powers of the maximal ideal meet in `0` and the action is faithful, the lower groups
meet in the trivial group. -/
theorem iInf_lowerGroup_eq_bot
    (hsep : ⨅ n, (maximalIdeal R) ^ n = ⊥) [FaithfulSMul G R] :
    ⨅ i, lowerGroup R G i = (⊥ : Subgroup G) := by
  refine le_bot_iff.mp fun σ hσ => ?_
  have h := iInf_lowerGroup_le_ker_toRingAut hsep hσ
  rw [MonoidHom.mem_ker] at h
  exact FaithfulSMul.eq_of_smul_eq_smul (α := R) fun x => by
    have := DFunLike.congr_fun h x; simpa using this.trans (one_smul G x).symm

end LocalRing

/-! ### Lower groups of a subgroup -/

section Subgroup

open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

section CompatibleHom

variable {H : Type*} [Group H] [MulSemiringAction H R]

/-- For a homomorphism `f : H →* G` compatible with the actions, `H_i` is the preimage of `G_i`. -/
theorem lowerGroup_comap_of_forall_smul_eq (f : H →* G)
    (hf : ∀ (h : H) (x : R), f h • x = h • x) (i : ℕ) :
    lowerGroup R H i = (lowerGroup R G i).comap f := by
  ext σ
  simp only [mem_lowerGroup, Subgroup.mem_comap, hf]

end CompatibleHom

theorem mem_lowerGroup_subgroup {H : Subgroup G} {σ : H} {i : ℕ} :
    σ ∈ lowerGroup R H i ↔ (σ : G) ∈ lowerGroup R G i :=
  Iff.rfl

/-- `H_i = G_i ∩ H` for a subgroup `H` (Serre, *Local Fields*, IV, §1). -/
@[simp]
theorem lowerGroup_subgroupOf (H : Subgroup G) (i : ℕ) :
    (lowerGroup R G i).subgroupOf H = lowerGroup R H i :=
  rfl

@[simp]
theorem lowerGroup_map_subtype (H : Subgroup G) (i : ℕ) :
    (lowerGroup R H i).map H.subtype = lowerGroup R G i ⊓ H := by
  rw [← lowerGroup_subgroupOf H i, Subgroup.subgroupOf_map_subtype]

theorem lowerGroup_map_subtype' (H : Subgroup G) (i : ℕ) :
    (lowerGroup R H i).map H.subtype = H ⊓ lowerGroup R G i := by
  rw [lowerGroup_map_subtype, inf_comm]

theorem lowerGroup_subgroup_eq_top_iff (H : Subgroup G) (i : ℕ) :
    lowerGroup R H i = ⊤ ↔ H ≤ lowerGroup R G i := by
  rw [← lowerGroup_subgroupOf H i, Subgroup.subgroupOf_eq_top]

theorem lowerGroup_comap_inclusion {H K : Subgroup G} (hHK : H ≤ K) (i : ℕ) :
    lowerGroup R H i =
      (lowerGroup R K i).comap (Subgroup.inclusion hHK) :=
  lowerGroup_comap_of_forall_smul_eq (Subgroup.inclusion hHK) (fun _ _ => rfl) i

theorem lowerGroup_map_subtype_le_map_subtype {H K : Subgroup G} (hHK : H ≤ K)
    (i : ℕ) :
    (lowerGroup R H i).map H.subtype ≤
      (lowerGroup R K i).map K.subtype := by
  rw [lowerGroup_map_subtype, lowerGroup_map_subtype]
  exact inf_le_inf_left _ hHK

end Subgroup

end Langlands.Ramification
