import Langlands.Algebra.RankOneGradedAlgebra

/-!
# Line stabilizers in a rank-one graded algebra acting on a vector space

Let `R = ⨁ 𝒜 i` be a `k`-algebra graded by an additive commutative group `ι`, with homogeneous
pieces of rank at most one and nonzero homogeneous elements invertible
(`IsRankOneGrading`). Let `ρ : R → End_k M` be a multiplicative or anti-multiplicative linear
action on a finite-dimensional `M` with `ρ 1 = 1` and every endomorphism of `M` in its image.

For `x ∈ M`, `stab x` is the subgroup of degrees `a` whose piece is nonzero and acts on `x`
by scalars, and `perp K` is the set of degrees whose piece commutes, through `ρ`, with every
piece of a degree of `K`. We prove:

* `radical_le_stab`, `stab_le_support`: `radical ≤ stab x ≤ support`;
* `commute_of_mem_stab`: for `x ≠ 0` the pieces of degrees in `stab x` act by commuting
  operators;
* `relIndex_stab_support`, `relIndex_radical_stab`: if `x ≠ 0` and `perp (stab x) ⊆ stab x`,
  then `stab x` has index `dim M` in the support and (in characteristic zero) the radical has
  index `dim M` in `stab x`;
* `exists_perp_subset_stab`: over an algebraically closed field of characteristic zero such an
  `x` exists.
-/

noncomputable section

open DirectSum

namespace Langlands.RankOneGraded

namespace IsRankOneGrading

variable {ι k R : Type*} [AddCommGroup ι] [DecidableEq ι] [Field k] [Ring R] [Algebra k R]
variable {𝒜 : ι → Submodule k R} [GradedAlgebra 𝒜] (h𝒜 : IsRankOneGrading 𝒜)
variable {M : Type*} [AddCommGroup M] [Module k M] {ρ : R →ₗ[k] Module.End k M}

include h𝒜

section Action

variable (hρ1 : ρ 1 = 1) (hρ : IsMulOrAntiMul ρ)
include hρ1 hρ

/-- A nonzero homogeneous element acts by an invertible operator. -/
theorem isUnit_map {a : ι} {u : R} (hu : u ∈ 𝒜 a) (hu0 : u ≠ 0) : IsUnit (ρ u) := by
  obtain ⟨v, -, huv, hvu⟩ := h𝒜.exists_inv_mem hu hu0
  have h1 : ρ (u * v) = 1 := by rw [huv, hρ1]
  have h2 : ρ (v * u) = 1 := by rw [hvu, hρ1]
  rcases hρ with h | h
  · rw [h] at h1 h2
    exact ⟨⟨ρ u, ρ v, h1, h2⟩, rfl⟩
  · rw [h] at h1 h2
    exact ⟨⟨ρ u, ρ v, h2, h1⟩, rfl⟩

theorem map_injective {a : ι} {u : R} (hu : u ∈ 𝒜 a) (hu0 : u ≠ 0) :
    Function.Injective (ρ u) :=
  ((Module.End.isUnit_iff _).mp (h𝒜.isUnit_map hρ1 hρ hu hu0)).1

end Action

section Mul

variable (hρ : IsMulOrAntiMul ρ)
include hρ

/-- The action of an element of degree `a + b` is a multiple of the product of the actions of
nonzero elements of degrees `a` and `b`. -/
theorem exists_map_eq_smul_mul [Nontrivial R] {a b : ι} {u v w : R} (hu : u ∈ 𝒜 a)
    (hu0 : u ≠ 0) (hv : v ∈ 𝒜 b) (hv0 : v ≠ 0) (hw : w ∈ 𝒜 (a + b)) :
    ∃ c : k, ρ w = c • (ρ u * ρ v) := by
  rcases hρ with h | h
  · obtain ⟨c, hc⟩ := h𝒜.exists_smul_eq (SetLike.mul_mem_graded hu hv)
      (h𝒜.mul_ne_zero hu hu0 hv0) hw
    exact ⟨c, by rw [← hc, map_smul, h]⟩
  · have hvu : v * u ∈ 𝒜 (a + b) := by
      rw [add_comm]
      exact SetLike.mul_mem_graded hv hu
    obtain ⟨c, hc⟩ := h𝒜.exists_smul_eq hvu (h𝒜.mul_ne_zero hv hv0 hu0) hw
    exact ⟨c, by rw [← hc, map_smul, h]⟩

/-- Commutation of the actions of homogeneous elements, up to a scalar. -/
theorem exists_map_mul_eq_smul [Nontrivial R] {a b : ι} {u v : R} (hu : u ∈ 𝒜 a)
    (hu0 : u ≠ 0) (hv : v ∈ 𝒜 b) :
    ∃ c : k, ρ v * ρ u = c • (ρ u * ρ v) := by
  by_cases hv0 : v = 0
  · exact ⟨0, by simp [hv0]⟩
  have hvu : v * u ∈ 𝒜 (a + b) := by
    rw [add_comm]
    exact SetLike.mul_mem_graded hv hu
  have huv : u * v ∈ 𝒜 (a + b) := SetLike.mul_mem_graded hu hv
  rcases hρ with h | h
  · obtain ⟨c, hc⟩ := h𝒜.exists_smul_eq huv (h𝒜.mul_ne_zero hu hu0 hv0) hvu
    exact ⟨c, by rw [← h, ← hc, map_smul, h]⟩
  · obtain ⟨c, hc⟩ := h𝒜.exists_smul_eq hvu (h𝒜.mul_ne_zero hv hv0 hu0) huv
    exact ⟨c, by rw [← h, ← hc, map_smul, h]⟩

end Mul

variable [Nontrivial R]

section Stab

variable (hρ1 : ρ 1 = 1) (hρ : IsMulOrAntiMul ρ)

variable (ρ) in
/-- The degrees whose (nonzero) piece acts on `x` by scalars: the stabilizer of the line through
`x`. -/
def stab (x : M) : AddSubgroup ι where
  carrier := {a | 𝒜 a ≠ ⊥ ∧ ∀ u ∈ 𝒜 a, ∃ c : k, ρ u x = c • x}
  zero_mem' := by
    refine ⟨h𝒜.support.zero_mem, fun u hu => ?_⟩
    obtain ⟨c, rfl⟩ := h𝒜.exists_algebraMap_eq_of_mem_zero hu
    refine ⟨c, ?_⟩
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hρ1]
    rfl
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨h𝒜.support.add_mem ha hb, fun w hw => ?_⟩
    obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp ha
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hb
    obtain ⟨c, hc⟩ := h𝒜.exists_map_eq_smul_mul hρ hu hu0 hv hv0 hw
    obtain ⟨d, hd⟩ := hb' v hv
    obtain ⟨e, he⟩ := ha' u hu
    refine ⟨c * d * e, ?_⟩
    rw [hc, LinearMap.smul_apply, Module.End.mul_apply, hd, map_smul, he, smul_smul,
      smul_smul]
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨h𝒜.support.neg_mem ha, fun w hw => ?_⟩
    by_cases hw0 : w = 0
    · exact ⟨0, by simp [hw0]⟩
    obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp ha
    have h1 : (1 : R) ∈ 𝒜 (-a + a) := by
      rw [neg_add_cancel]
      exact SetLike.GradedOne.one_mem
    obtain ⟨c, hc⟩ := h𝒜.exists_map_eq_smul_mul hρ hw hw0 hu hu0 h1
    obtain ⟨e, he⟩ := ha' u hu
    have hx : x = (c * e) • ρ w x := by
      calc x = ρ 1 x := by rw [hρ1]; rfl
        _ = (c * e) • ρ w x := by
          rw [hc, LinearMap.smul_apply, Module.End.mul_apply, he, map_smul, smul_smul]
    by_cases hce : c * e = 0
    · refine ⟨0, ?_⟩
      rw [hce, zero_smul] at hx
      rw [hx, map_zero, smul_zero]
    · refine ⟨(c * e)⁻¹, ?_⟩
      conv_rhs => rw [hx]
      rw [smul_smul, inv_mul_cancel₀ hce, one_smul]

theorem mem_stab_iff {x : M} {a : ι} :
    a ∈ h𝒜.stab ρ hρ1 hρ x ↔ 𝒜 a ≠ ⊥ ∧ ∀ u ∈ 𝒜 a, ∃ c : k, ρ u x = c • x :=
  Iff.rfl

omit h𝒜 [Nontrivial R] in
variable (𝒜 ρ) in
/-- The degrees whose (nonzero) piece commutes, through `ρ`, with every piece of a degree of
`K`. -/
def perp (K : AddSubgroup ι) : Set ι :=
  {a | 𝒜 a ≠ ⊥ ∧ ∀ b ∈ K, ∀ u ∈ 𝒜 a, ∀ v ∈ 𝒜 b, ρ u * ρ v = ρ v * ρ u}

omit h𝒜 [Nontrivial R] [DecidableEq ι] [GradedAlgebra 𝒜] in
theorem mem_perp_iff {K : AddSubgroup ι} {a : ι} :
    a ∈ perp 𝒜 ρ K ↔ 𝒜 a ≠ ⊥ ∧ ∀ b ∈ K, ∀ u ∈ 𝒜 a, ∀ v ∈ 𝒜 b, ρ u * ρ v = ρ v * ρ u :=
  Iff.rfl

theorem stab_le_support (x : M) : h𝒜.stab ρ hρ1 hρ x ≤ h𝒜.support := fun _ ha => ha.1

/-- The radical acts by scalars, so it stabilizes every line. -/
theorem radical_le_stab (hsurj : Function.Surjective ρ) (x : M) :
    h𝒜.radical ≤ h𝒜.stab ρ hρ1 hρ x := by
  rintro a ⟨ha, ha'⟩
  refine ⟨ha, fun u hu => ?_⟩
  obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_mem_center hρ hsurj (ha' u hu)
  refine ⟨c, ?_⟩
  rw [hc, Algebra.algebraMap_eq_smul_one]
  rfl

/-- For `x ≠ 0`, the pieces of degrees in `stab x` act by commuting operators. -/
theorem commute_of_mem_stab {x : M} (hx : x ≠ 0) {a b : ι} (ha : a ∈ h𝒜.stab ρ hρ1 hρ x)
    (hb : b ∈ h𝒜.stab ρ hρ1 hρ x) {u v : R} (hu : u ∈ 𝒜 a) (hv : v ∈ 𝒜 b) :
    ρ u * ρ v = ρ v * ρ u := by
  by_cases hu0 : u = 0
  · simp [hu0]
  by_cases hv0 : v = 0
  · simp [hv0]
  obtain ⟨c, hc⟩ := h𝒜.exists_map_mul_eq_smul hρ hu hu0 hv
  obtain ⟨e, he⟩ := ha.2 u hu
  obtain ⟨d, hd⟩ := hb.2 v hv
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [zero_smul] at he
    exact hx (h𝒜.map_injective hρ1 hρ hu hu0 (he.trans (map_zero _).symm))
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hd
    exact hx (h𝒜.map_injective hρ1 hρ hv hv0 (hd.trans (map_zero _).symm))
  have h1 := congrArg (fun T : Module.End k M => T x) hc
  simp only [LinearMap.smul_apply, Module.End.mul_apply, he, hd, map_smul, smul_smul] at h1
  have hc1 : c = 1 := by
    have h2 : (e * d - c * (d * e)) • x = 0 := by rw [sub_smul, h1, sub_self]
    have h3 := (smul_eq_zero.mp h2).resolve_right hx
    have hed : e * d ≠ 0 := _root_.mul_ne_zero he0 hd0
    have : (1 - c) * (e * d) = 0 := by rw [← h3]; ring
    exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hed)).symm
  rw [hc, hc1, one_smul]

end Stab

section Transport

variable (hρ1 : ρ 1 = 1) (hρ : IsMulOrAntiMul ρ)
include hρ1 hρ

omit hρ1 [Nontrivial R] in
/-- Every homogeneous element acts as a homogeneous operator composed with a given nonzero
homogeneous element, on the left. -/
theorem exists_mem_map_mul_left {a a' : ι} {u u' : R} (hu : u ∈ 𝒜 a) (hu0 : u ≠ 0)
    (hu' : u' ∈ 𝒜 a') : ∃ w ∈ 𝒜 (a' - a), ρ w * ρ u = ρ u' := by
  obtain ⟨v, hv, huv, hvu⟩ := h𝒜.exists_inv_mem hu hu0
  rcases hρ with h | h
  · refine ⟨u' * v, ?_, ?_⟩
    · rw [sub_eq_add_neg]
      exact SetLike.mul_mem_graded hu' hv
    · rw [← h, mul_assoc, hvu, mul_one]
  · refine ⟨v * u', ?_, ?_⟩
    · rw [sub_eq_neg_add]
      exact SetLike.mul_mem_graded hv hu'
    · rw [← h, ← mul_assoc, huv, one_mul]

omit hρ1 [Nontrivial R] in
/-- Every homogeneous element acts as a given nonzero homogeneous element composed with a
homogeneous operator, on the right. -/
theorem exists_mem_map_mul_right {a a' : ι} {u u' : R} (hu : u ∈ 𝒜 a) (hu0 : u ≠ 0)
    (hu' : u' ∈ 𝒜 a') : ∃ w ∈ 𝒜 (a' - a), ρ u * ρ w = ρ u' := by
  obtain ⟨v, hv, huv, hvu⟩ := h𝒜.exists_inv_mem hu hu0
  rcases hρ with h | h
  · refine ⟨v * u', ?_, ?_⟩
    · rw [sub_eq_neg_add]
      exact SetLike.mul_mem_graded hv hu'
    · rw [← h, ← mul_assoc, huv, one_mul]
  · refine ⟨u' * v, ?_, ?_⟩
    · rw [sub_eq_add_neg]
      exact SetLike.mul_mem_graded hu' hv
    · rw [← h, mul_assoc, hvu, mul_one]

/-- If `b ∈ stab x`, the pieces of degree `b` act on each `ρ u x` (with `u` homogeneous and
nonzero) by scalars. -/
theorem exists_map_map_eq_smul {x : M} {a b : ι} (hb : b ∈ h𝒜.stab ρ hρ1 hρ x) {u v : R}
    (hu : u ∈ 𝒜 a) (hu0 : u ≠ 0) (hv : v ∈ 𝒜 b) : ∃ c : k, ρ v (ρ u x) = c • ρ u x := by
  obtain ⟨c, hc⟩ := h𝒜.exists_map_mul_eq_smul hρ hu hu0 hv
  obtain ⟨d, hd⟩ := hb.2 v hv
  refine ⟨c * d, ?_⟩
  rw [← Module.End.mul_apply, hc, LinearMap.smul_apply, Module.End.mul_apply, hd, map_smul,
    smul_smul]

end Transport

section Index

variable [FiniteDimensional k M] (hρ1 : ρ 1 = 1) (hρ : IsMulOrAntiMul ρ)

/-- **Index of a self-perpendicular line stabilizer in the support.** If `x ≠ 0` and every
degree whose piece commutes with the pieces of `stab x` lies in `stab x`, then `stab x` has
index `dim M` in the support. -/
theorem relIndex_stab_support (hsurj : Function.Surjective ρ) {x : M} (hx : x ≠ 0)
    (hperp : perp 𝒜 ρ (h𝒜.stab ρ hρ1 hρ x) ⊆ h𝒜.stab ρ hρ1 hρ x) :
    (h𝒜.stab ρ hρ1 hρ x).relIndex h𝒜.support = Module.finrank k M := by
  classical
  set S := h𝒜.stab ρ hρ1 hρ x with hS
  let Q := h𝒜.support ⧸ S.addSubgroupOf h𝒜.support
  let r : Q → ι := fun q => ((Quotient.out q : h𝒜.support) : ι)
  have hr : ∀ q, r q ∈ h𝒜.support := fun q => (Quotient.out q).2
  choose u hu hu0 using fun q => (h𝒜.mem_support_iff).mp (hr q)
  let y : Q → M := fun q => ρ (u q) x
  have hy0 : ∀ q, y q ≠ 0 := fun q h =>
    hx (h𝒜.map_injective hρ1 hρ (hu q) (hu0 q) (h.trans (map_zero _).symm))
  let J := {v : R // ∃ b ∈ S, v ∈ 𝒜 b}
  let f : J → Module.End k M := fun v => ρ v
  have hcomm : ∀ v w : J, Commute (f v) (f w) := by
    rintro ⟨v, b, hb, hv⟩ ⟨w, c, hc, hw⟩
    exact h𝒜.commute_of_mem_stab hρ1 hρ hx hb hc hv hw
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
    fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ
  have hev : ∀ q (v : J), ∃ c : k, ρ v (y q) = c • y q := by
    rintro q ⟨v, b, hb, hv⟩
    exact h𝒜.exists_map_map_eq_smul hρ1 hρ hb (hu q) (hu0 q) hv
  choose χ hχ using hev
  have hmem : ∀ q, y q ∈ ⨅ v, (f v).maxGenEigenspace (χ q v) := fun q =>
    Submodule.mem_iInf _ |>.mpr fun v =>
      Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr (hχ q v))
  have hχinj : Function.Injective χ := by
    intro q q' hqq'
    obtain ⟨w, hw, hw'⟩ := h𝒜.exists_mem_map_mul_left hρ (hu q) (hu0 q) (hu q')
    have hyq' : y q' = ρ w (y q) := by
      change ρ (u q') x = ρ w (ρ (u q) x)
      rw [← hw']
      rfl
    have hw0 : w ≠ 0 := by
      rintro rfl
      apply hy0 q'
      rw [hyq', map_zero, LinearMap.zero_apply]
    have hmemperp : r q' - r q ∈ perp 𝒜 ρ S := by
      refine ⟨(Submodule.ne_bot_iff _).mpr ⟨w, hw, hw0⟩, fun b hb w' hw'' v hv => ?_⟩
      obtain ⟨c', rfl⟩ := h𝒜.exists_smul_eq hw hw0 hw''
      suffices ρ w * ρ v = ρ v * ρ w by
        rw [map_smul, smul_mul_assoc, mul_smul_comm, this]
      by_cases hv0 : v = 0
      · simp [hv0]
      obtain ⟨c, hc⟩ := h𝒜.exists_map_mul_eq_smul hρ hw hw0 hv
      have h1 : ρ v (y q) = χ q ⟨v, b, hb, hv⟩ • y q := hχ q ⟨v, b, hb, hv⟩
      have h2 : ρ v (y q') = χ q' ⟨v, b, hb, hv⟩ • y q' := hχ q' ⟨v, b, hb, hv⟩
      rw [← hqq'] at h2
      set μ := χ q ⟨v, b, hb, hv⟩
      have hμ0 : μ ≠ 0 := by
        intro h0
        rw [h0, zero_smul] at h1
        exact hy0 q (h𝒜.map_injective hρ1 hρ hv hv0 (h1.trans (map_zero _).symm))
      have h3 : ρ v (y q') = (c * μ) • y q' := by
        rw [hyq', ← Module.End.mul_apply, hc, LinearMap.smul_apply, Module.End.mul_apply, h1,
          map_smul, smul_smul]
      have h4 : (c * μ - μ) • y q' = 0 := by rw [sub_smul, ← h3, h2, sub_self]
      have h5 := (smul_eq_zero.mp h4).resolve_right (hy0 q')
      have hc1 : c = 1 := by
        have : (c - 1) * μ = 0 := by rw [← h5]; ring
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hμ0)
      rw [hc, hc1, one_smul]
    have hS' := hperp hmemperp
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq,
      AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add, AddSubgroup.coe_neg, neg_add_eq_sub]
    exact hS'
  have hli : LinearIndependent k y :=
    iSupIndep.linearIndependent _ (hind.comp hχinj) hmem hy0
  have hspan : ⊤ ≤ Submodule.span k (Set.range y) := by
    rintro z -
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k hx
    obtain ⟨t, ht⟩ := hsurj (LinearMap.smulRight φ z)
    have hz : z = ρ t x := by rw [ht, LinearMap.smulRight_apply, hφ, one_smul]
    rw [hz]
    clear ht hz
    induction t using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero =>
      rw [map_zero, LinearMap.zero_apply]
      exact Submodule.zero_mem _
    | add a b ha hb =>
      rw [map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ ha hb
    | @homogeneous i m =>
      by_cases hm : (m : R) = 0
      · rw [hm, map_zero, LinearMap.zero_apply]
        exact Submodule.zero_mem _
      have hi : i ∈ h𝒜.support := (h𝒜.mem_support_iff).mpr ⟨m, m.2, hm⟩
      have hiS : i - r (QuotientAddGroup.mk ⟨i, hi⟩) ∈ S := by
        have h := QuotientAddGroup.out_eq' (QuotientAddGroup.mk ⟨i, hi⟩ : Q)
        rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add,
          AddSubgroup.coe_neg, neg_add_eq_sub] at h
        exact h
      obtain ⟨w, hw, hw'⟩ := h𝒜.exists_mem_map_mul_right hρ
        (hu (QuotientAddGroup.mk ⟨i, hi⟩)) (hu0 _) m.2
      obtain ⟨d, hd⟩ := hiS.2 w hw
      rw [← hw', Module.End.mul_apply, hd, map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have : Finite Q := hli.finite
  change Nat.card Q = _
  rw [Module.finrank_eq_nat_card_basis (Module.Basis.mk hli hspan)]

/-- **Index of the radical in a self-perpendicular line stabilizer.** Under the hypotheses of
`relIndex_stab_support`, the radical has index `dim M` in `stab x`. -/
theorem relIndex_radical_stab [CharZero k] (hsurj : Function.Surjective ρ) {x : M} (hx : x ≠ 0)
    (hperp : perp 𝒜 ρ (h𝒜.stab ρ hρ1 hρ x) ⊆ h𝒜.stab ρ hρ1 hρ x) :
    h𝒜.radical.relIndex (h𝒜.stab ρ hρ1 hρ x) = Module.finrank k M := by
  have : Nontrivial M := ⟨⟨x, 0, hx⟩⟩
  have h1 := AddSubgroup.relIndex_mul_relIndex h𝒜.radical (h𝒜.stab ρ hρ1 hρ x) h𝒜.support
    (h𝒜.radical_le_stab hρ1 hρ hsurj x) (h𝒜.stab_le_support hρ1 hρ x)
  have h2 : h𝒜.radical.relIndex h𝒜.support = Module.finrank k M ^ 2 :=
    (h𝒜.finite_cosets_and_card_eq hρ1 hρ hsurj).2
  rw [h𝒜.relIndex_stab_support hρ1 hρ hsurj hx hperp, h2, sq] at h1
  exact Nat.eq_of_mul_eq_mul_right Module.finrank_pos h1

end Index

section Exists

variable [FiniteDimensional k M] [Nontrivial M] (hρ1 : ρ 1 = 1) (hρ : IsMulOrAntiMul ρ)

omit [Nontrivial M] in
/-- If a degree outside `stab x₀` has a piece commuting with the pieces of `stab x₀`, then over
an algebraically closed field some nonzero `y` has a strictly larger stabilizer. -/
theorem exists_stab_gt [IsAlgClosed k] {x₀ : M} (hx₀ : x₀ ≠ 0) {a : ι}
    (ha : a ∈ perp 𝒜 ρ (h𝒜.stab ρ hρ1 hρ x₀)) :
    ∃ y : M, y ≠ 0 ∧ h𝒜.stab ρ hρ1 hρ x₀ ≤ h𝒜.stab ρ hρ1 hρ y ∧
      a ∈ h𝒜.stab ρ hρ1 hρ y := by
  classical
  set S := h𝒜.stab ρ hρ1 hρ x₀ with hS
  let J := {v : R // ∃ b ∈ S, v ∈ 𝒜 b}
  have hev : ∀ v : J, ∃ c : k, ρ v x₀ = c • x₀ := by
    rintro ⟨v, b, hb, hv⟩
    exact hb.2 v hv
  choose χ hχ using hev
  let E : Submodule k M := ⨅ v : J, Module.End.eigenspace (ρ v) (χ v)
  have hmemE : ∀ z, z ∈ E ↔ ∀ v : J, ρ v z = χ v • z := fun z => by
    simp only [E, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  have hx₀E : x₀ ∈ E := (hmemE x₀).mpr hχ
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp ha.1
  have hmaps : Set.MapsTo (ρ u) E E := by
    intro z hz
    rw [SetLike.mem_coe, hmemE] at hz ⊢
    rintro ⟨v, b, hb, hv⟩
    have hcomm := ha.2 b hb u hu v hv
    change ρ v (ρ u z) = χ ⟨v, b, hb, hv⟩ • ρ u z
    rw [← Module.End.mul_apply, ← hcomm, Module.End.mul_apply, hz ⟨v, b, hb, hv⟩, map_smul]
  have : Nontrivial E := ⟨⟨⟨x₀, hx₀E⟩, 0, fun h => hx₀ (congrArg Subtype.val h)⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((ρ u).restrict hmaps)
  obtain ⟨z, hz⟩ := hc.exists_hasEigenvector
  have hz0 : (z : M) ≠ 0 := fun h => hz.2 (Subtype.ext h)
  have hzu : ρ u z = c • (z : M) := congrArg Subtype.val hz.apply_eq_smul
  refine ⟨z, hz0, fun b hb => ⟨hb.1, fun v hv => ⟨χ ⟨v, b, hb, hv⟩, ?_⟩⟩, ha.1, fun u' hu' => ?_⟩
  · exact (hmemE z).mp z.2 ⟨v, b, hb, hv⟩
  · obtain ⟨c', rfl⟩ := h𝒜.exists_smul_eq hu hu0 hu'
    exact ⟨c' * c, by rw [map_smul, LinearMap.smul_apply, hzu, smul_smul]⟩

/-- **Existence of a self-perpendicular line.** Over an algebraically closed field of
characteristic zero, some nonzero `x` satisfies `perp (stab x) ⊆ stab x`. -/
theorem exists_perp_subset_stab [IsAlgClosed k] [CharZero k] (hsurj : Function.Surjective ρ) :
    ∃ x : M, x ≠ 0 ∧ perp 𝒜 ρ (h𝒜.stab ρ hρ1 hρ x) ⊆ h𝒜.stab ρ hρ1 hρ x := by
  classical
  have hrad : h𝒜.radical.relIndex h𝒜.support ≠ 0 := by
    have h2 : h𝒜.radical.relIndex h𝒜.support = Module.finrank k M ^ 2 :=
      (h𝒜.finite_cosets_and_card_eq hρ1 hρ hsurj).2
    rw [h2]
    exact pow_ne_zero _ Module.finrank_pos.ne'
  have hne : ∀ x : M, (h𝒜.stab ρ hρ1 hρ x).relIndex h𝒜.support ≠ 0 := fun x h =>
    hrad (AddSubgroup.relIndex_eq_zero_of_le_left (h𝒜.radical_le_stab hρ1 hρ hsurj x) h)
  have hP : ∃ n, ∃ x : M, x ≠ 0 ∧ (h𝒜.stab ρ hρ1 hρ x).relIndex h𝒜.support = n := by
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    exact ⟨_, x, hx, rfl⟩
  obtain ⟨x₀, hx₀, hn⟩ := Nat.find_spec hP
  refine ⟨x₀, hx₀, fun a ha => ?_⟩
  by_contra haS
  obtain ⟨y, hy0, hle, hay⟩ := h𝒜.exists_stab_gt hρ1 hρ hx₀ ha
  have hmul := AddSubgroup.relIndex_mul_relIndex (h𝒜.stab ρ hρ1 hρ x₀) (h𝒜.stab ρ hρ1 hρ y)
    h𝒜.support hle (h𝒜.stab_le_support hρ1 hρ y)
  have h1 : (h𝒜.stab ρ hρ1 hρ x₀).relIndex (h𝒜.stab ρ hρ1 hρ y) ≠ 1 := fun h =>
    haS (AddSubgroup.relIndex_eq_one.mp h hay)
  have h0 : (h𝒜.stab ρ hρ1 hρ x₀).relIndex (h𝒜.stab ρ hρ1 hρ y) ≠ 0 := fun h => by
    rw [h, zero_mul] at hmul
    exact hne x₀ hmul.symm
  have hlt : (h𝒜.stab ρ hρ1 hρ y).relIndex h𝒜.support < Nat.find hP := by
    rw [← hn, ← hmul]
    have := hne y
    have h2 : 2 ≤ (h𝒜.stab ρ hρ1 hρ x₀).relIndex (h𝒜.stab ρ hρ1 hρ y) := by omega
    nlinarith [Nat.pos_of_ne_zero this]
  exact Nat.find_min hP hlt ⟨y, hy0, rfl⟩

end Exists

end IsRankOneGrading

end Langlands.RankOneGraded
