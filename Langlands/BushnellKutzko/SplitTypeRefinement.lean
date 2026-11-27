import Langlands.Representation.Jacquet.Coinvariants
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-! # Jacquet nonvanishing by refinement along a filtration

Two abstract steps of the proof of Bushnell–Kutzko (8.2.5)(iv): the descent along an
exhaustive antitone family of subgroups of a unipotent radical, and the passage from a vector
on which a subgroup `𝒦` acts by a character to a vector on which a larger group `K` acts by a
character, using a family of conjugating elements whose conjugate characters average to the
indicator of `𝒦`.
-/

noncomputable section

open scoped BigOperators

namespace Langlands.Jacquet

universe uG uV uZ

variable {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Coinvariant relations grow with the subgroup. -/
theorem relations_mono (ρ : Representation ℂ G V) {N N' : Subgroup G} (h : N ≤ N') :
    relations ρ N ≤ relations ρ N' := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨n, v⟩, rfl⟩
  exact Representation.Coinvariants.mem_ker_of_eq (ρ := ρ.comp N'.subtype)
    (⟨n, h n.2⟩ : N') v _ rfl

/-- Conjugation by `g` carries the relations of `N` to those of `g N g⁻¹`, stated for a
subgroup `N'` containing that conjugate. -/
theorem apply_mem_relations (ρ : Representation ℂ G V) {N N' : Subgroup G} (g : G)
    (h : ∀ n ∈ N, g * n * g⁻¹ ∈ N') {v : V} (hv : v ∈ relations ρ N) :
    ρ g v ∈ relations ρ N' := by
  have hle : relations ρ N ≤ (relations ρ N').comap (ρ g) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨n, x⟩, rfl⟩
    change ρ g (ρ n x - x) ∈ relations ρ N'
    refine Representation.Coinvariants.mem_ker_of_eq (ρ := ρ.comp N'.subtype)
      (⟨g * n * g⁻¹, h n n.2⟩ : N') (ρ g x) _ ?_
    change ρ (g * n * g⁻¹) (ρ g x) - ρ g x = ρ g (ρ n x - x)
    rw [map_sub, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
      inv_mul_cancel_right]
  exact hle hv

/-- A relation for a subgroup exhausted by an antitone family is a relation for one member. -/
theorem exists_mem_relations_of_exhaustive (ρ : Representation ℂ G V) (U : Subgroup G)
    (M : ℤ → Subgroup G) (hanti : Antitone M) (hexh : ∀ u ∈ U, ∃ j, u ∈ M j)
    {v : V} (hv : v ∈ relations ρ U) : ∃ j, v ∈ relations ρ (M j) := by
  classical
  obtain ⟨T, hT, hvT⟩ := Submodule.mem_span_finite_of_mem_span hv
  have key : ∀ T' : Finset V, (↑T' : Set V) ⊆
      Set.range (fun nv : U × V => ρ nv.1 nv.2 - nv.2) →
      ∃ j, (↑T' : Set V) ⊆ relations ρ (M j) := by
    intro T'
    induction T' using Finset.induction_on with
    | empty => exact fun _ => ⟨0, by simp⟩
    | insert t T' _ ih =>
      intro hsub
      rw [Finset.coe_insert, Set.insert_subset_iff] at hsub
      obtain ⟨j₁, hj₁⟩ := ih hsub.2
      obtain ⟨⟨u, x⟩, hux⟩ := hsub.1
      obtain ⟨j₂, hj₂⟩ := hexh u u.2
      refine ⟨min j₁ j₂, ?_⟩
      rw [Finset.coe_insert, Set.insert_subset_iff]
      refine ⟨?_, fun y hy => relations_mono ρ (hanti (min_le_left j₁ j₂)) (hj₁ hy)⟩
      exact Representation.Coinvariants.mem_ker_of_eq (ρ := ρ.comp (M (min j₁ j₂)).subtype)
        (⟨u, hanti (min_le_right j₁ j₂) hj₂⟩ : M (min j₁ j₂)) x t hux
  obtain ⟨j, hj⟩ := key T hT
  exact ⟨j, (Submodule.span_le.mpr hj) hvT⟩

/-- **Descent along a filtration.** Let `M` be an antitone family of subgroups exhausting `U`,
and `P` a finite-dimensional subspace. If `P` is not contained in the relations of `M j₀`, and
non-containment for `M j` implies non-containment for `M (j - 1)`, then `P` is not contained in
the relations of `U`. -/
theorem not_le_relations_of_refinement (ρ : Representation ℂ G V) (U : Subgroup G)
    (M : ℤ → Subgroup G) (hanti : Antitone M) (hexh : ∀ u ∈ U, ∃ j, u ∈ M j)
    (P : Submodule ℂ V) [FiniteDimensional ℂ P] (j₀ : ℤ)
    (h₀ : ¬ P ≤ relations ρ (M j₀))
    (hstep : ∀ j, ¬ P ≤ relations ρ (M j) → ¬ P ≤ relations ρ (M (j - 1))) :
    ¬ P ≤ relations ρ U := by
  have hdesc : ∀ k : ℕ, ¬ P ≤ relations ρ (M (j₀ - k)) := by
    intro k
    induction k with
    | zero => simpa using h₀
    | succ k ih =>
      have h := hstep _ ih
      rwa [show j₀ - (k : ℤ) - 1 = j₀ - ((k + 1 : ℕ) : ℤ) by push_cast; ring] at h
  intro hPU
  let b := Module.finBasis ℂ P
  have hbj : ∀ i, ∃ j, ((b i : P) : V) ∈ relations ρ (M j) := fun i =>
    exists_mem_relations_of_exhaustive ρ U M hanti hexh (hPU (b i).2)
  choose j hj using hbj
  let k : ℕ := ∑ i, (j₀ - j i).toNat
  apply hdesc k
  have hle : ∀ i, j₀ - (k : ℤ) ≤ j i := by
    intro i
    have h1 : (j₀ - j i).toNat ≤ k :=
      Finset.single_le_sum (f := fun i => (j₀ - j i).toNat) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    have h2 : j₀ - j i ≤ ((j₀ - j i).toNat : ℤ) := Int.self_le_toNat _
    omega
  have hspan : P = Submodule.span ℂ (Set.range fun i => ((b i : P) : V)) := by
    have hr : (Set.range fun i => ((b i : P) : V)) = P.subtype '' Set.range b := by
      rw [← Set.range_comp]
      rfl
    rw [hr, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  rw [hspan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact relations_mono ρ (hanti (hle i)) (hj i)

/-- Non-containment in the relations of `U` gives nonzero coinvariants. -/
theorem not_subsingleton_of_not_le_relations (ρ : Representation ℂ G V) (U : Subgroup G)
    {P : Submodule ℂ V} (hP : ¬ P ≤ relations ρ U) : ¬ Subsingleton (Coinvariants ρ U) := by
  intro hs
  apply hP
  intro v _
  rw [← mk_eq_zero]
  exact Subsingleton.elim _ _

section Transfer

variable (ρ : Representation ℂ G V) (K 𝒦 : Subgroup G)

/-- The twisted coset sum `∑_{c ∈ K/𝒦} χ(c)⁻¹ ρ(c) v`, computed with chosen representatives. -/
def twistedCosetSum [Fintype (K ⧸ 𝒦.subgroupOf K)] (χ : K →* ℂˣ) (v : V) : V :=
  ∑ q : K ⧸ 𝒦.subgroupOf K, (((χ q.out)⁻¹ : ℂˣ) : ℂ) • ρ (q.out : G) v

variable {ρ K 𝒦}

/-- If the elements of `K` lying in `𝒦` act on `v` through the character `χ`, the twisted
coset sum is `χ`-isotypic for `K`. -/
theorem twistedCosetSum_isotypic [Fintype (K ⧸ 𝒦.subgroupOf K)] (χ : K →* ℂˣ) {v : V}
    (hv : ∀ κ : K, (κ : G) ∈ 𝒦 → ρ κ v = (χ κ : ℂ) • v) (k : K) :
    ρ k (twistedCosetSum ρ K 𝒦 χ v) = (χ k : ℂ) • twistedCosetSum ρ K 𝒦 χ v := by
  classical
  unfold twistedCosetSum
  rw [map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (MulAction.toPerm k) _ _ fun q => ?_
  -- compare the representatives of `q` and `k • q`
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (𝒦.subgroupOf K) (k * q.out)
  have hkq : (QuotientGroup.mk (k * q.out) : K ⧸ 𝒦.subgroupOf K) = k • q := by
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [hkq] at hh
  set q' : K ⧸ 𝒦.subgroupOf K := k • q with hq'
  set κ : K := ((h⁻¹ : 𝒦.subgroupOf K) : K) with hκdef
  have hrep : (k * q.out : K) = q'.out * κ := by
    rw [hh, hκdef, Subgroup.coe_inv, mul_inv_cancel_right]
  have hκ : (κ : G) ∈ 𝒦 := (h⁻¹).2
  have hρ : ρ ((k : G) * (q.out : G)) v = (χ κ : ℂ) • ρ (q'.out : G) v := by
    have hG : (k : G) * (q.out : G) = (q'.out : G) * (κ : G) := by
      have := congrArg (fun x : K => (x : G)) hrep
      simpa using this
    rw [hG, map_mul, Module.End.mul_apply, hv _ hκ, map_smul]
  have hχ : (χ k : ℂ) * χ q.out = (χ q'.out : ℂ) * χ κ := by
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, hrep]
  change ρ k ((((χ q.out)⁻¹ : ℂˣ) : ℂ) • ρ (q.out : G) v) =
    (χ k : ℂ) • ((((χ q'.out)⁻¹ : ℂˣ) : ℂ) • ρ (q'.out : G) v)
  rw [map_smul, ← Module.End.mul_apply, ← map_mul, hρ, smul_smul, smul_smul]
  congr 1
  have h1 : (χ q.out : ℂ) ≠ 0 := Units.ne_zero _
  have h3 : (χ q'.out : ℂ) ≠ 0 := Units.ne_zero _
  rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val]
  field_simp
  linear_combination hχ.symm

open scoped Classical in
/-- **Transfer of non-vanishing.** Let `v ∉ rel(M)` be a vector on which the elements of `K`
lying in `𝒦` act through `ϑ`, and let `(χ_z, g_z)` be a nonempty finite family of characters
of `K` agreeing with `ϑ` on `K ∩ 𝒦` and of elements with `g_z⁻¹ M g_z ⊆ M` carrying
`χ_z`-isotypic vectors to `ϑ`-isotypic ones. If `∑_z χ_z(k)⁻¹` is `|Z| ϑ(k)⁻¹` on `K ∩ 𝒦`
and `0` on the rest of `K`, then some `ϑ`-isotypic vector for `K` is not in `rel(M)`. -/
theorem exists_isotypic_not_mem_relations [Fintype (K ⧸ 𝒦.subgroupOf K)]
    (M : Subgroup G) (ϑ : K →* ℂˣ) {Z : Type uZ} [Fintype Z] [Nonempty Z]
    (χ : Z → K →* ℂˣ) (g : Z → G)
    (hχ𝒦 : ∀ z (k : K), (k : G) ∈ 𝒦 → χ z k = ϑ k)
    (horth : ∀ k : K, ∑ z, (((χ z k)⁻¹ : ℂˣ) : ℂ) =
      if (k : G) ∈ 𝒦 then (Fintype.card Z : ℂ) * (((ϑ k)⁻¹ : ℂˣ) : ℂ) else 0)
    (hg : ∀ z (w : V), (∀ k : K, ρ k w = (χ z k : ℂ) • w) →
      ∀ k : K, ρ k (ρ (g z) w) = (ϑ k : ℂ) • ρ (g z) w)
    (hgM : ∀ z, ∀ m ∈ M, (g z)⁻¹ * m * (g z)⁻¹⁻¹ ∈ M)
    {v : V} (hv : ∀ κ : K, (κ : G) ∈ 𝒦 → ρ κ v = (ϑ κ : ℂ) • v)
    (hvM : v ∉ relations ρ M) :
    ∃ w : V, (∀ k : K, ρ k w = (ϑ k : ℂ) • w) ∧ w ∉ relations ρ M := by
  classical
  have hvz : ∀ z (κ : K), (κ : G) ∈ 𝒦 → ρ κ v = (χ z κ : ℂ) • v := fun z κ hκ => by
    rw [hχ𝒦 z κ hκ, hv κ hκ]
  -- the sum of the twisted coset sums is `|Z| v`
  have hsum : ∑ z, twistedCosetSum ρ K 𝒦 (χ z) v = (Fintype.card Z : ℂ) • v := by
    unfold twistedCosetSum
    rw [Finset.sum_comm]
    have hfac : ∀ q : K ⧸ 𝒦.subgroupOf K, ∑ z, (((χ z q.out)⁻¹ : ℂˣ) : ℂ) • ρ (q.out : G) v =
        (∑ z, (((χ z q.out)⁻¹ : ℂˣ) : ℂ)) • ρ (q.out : G) v := fun q => by
      rw [Finset.sum_smul]
    rw [Finset.sum_congr rfl fun q _ => hfac q]
    have hmem1 : ∀ q : K ⧸ 𝒦.subgroupOf K, (((q.out : K) : G) ∈ 𝒦 ↔
        q = ((1 : K) : K ⧸ 𝒦.subgroupOf K)) := by
      intro q
      constructor
      · intro hmem
        rw [← QuotientGroup.out_eq' q]
        apply QuotientGroup.eq.mpr
        rw [Subgroup.mem_subgroupOf, mul_one, Subgroup.coe_inv, inv_mem_iff]
        exact hmem
      · rintro rfl
        have h2 := QuotientGroup.eq.mp (QuotientGroup.out_eq' ((1 : K) : K ⧸ 𝒦.subgroupOf K))
        rw [Subgroup.mem_subgroupOf, mul_one, Subgroup.coe_inv, inv_mem_iff] at h2
        exact h2
    rw [Finset.sum_eq_single ((1 : K) : K ⧸ 𝒦.subgroupOf K)]
    · have hout := (hmem1 ((1 : K) : K ⧸ 𝒦.subgroupOf K)).mpr rfl
      rw [horth]
      simp only [hout, ↓reduceIte]
      rw [hv _ hout, smul_smul, Units.val_inv_eq_inv_val, mul_assoc,
        inv_mul_cancel₀ (Units.ne_zero _), mul_one]
    · intro q _ hq
      have hout : (((q.out : K) : G)) ∉ 𝒦 := fun hmem => hq ((hmem1 q).mp hmem)
      rw [horth]
      simp only [hout, ↓reduceIte, zero_smul]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  -- some twisted coset sum is not a relation
  have hex : ∃ z, twistedCosetSum ρ K 𝒦 (χ z) v ∉ relations ρ M := by
    by_contra hall
    push Not at hall
    apply hvM
    have hmem : (Fintype.card Z : ℂ) • v ∈ relations ρ M := by
      rw [← hsum]
      exact Submodule.sum_mem _ fun z _ => hall z
    have hcard : (Fintype.card Z : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simpa [smul_smul, inv_mul_cancel₀ hcard] using
      (relations ρ M).smul_mem (Fintype.card Z : ℂ)⁻¹ hmem
  obtain ⟨z, hz⟩ := hex
  refine ⟨ρ (g z) (twistedCosetSum ρ K 𝒦 (χ z) v),
    hg z _ (twistedCosetSum_isotypic (χ z) (hvz z)), fun hmem => hz ?_⟩
  have h := apply_mem_relations ρ (g z)⁻¹ (hgM z) hmem
  rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h

end Transfer

end Langlands.Jacquet
