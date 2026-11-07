import Mathlib

/-!
# Algebras graded by a commutative group with pieces of rank at most one

A `k`-algebra `R` with a grading `R = ⨁ i, 𝒜 i` over an additive commutative group `ι`,
whose homogeneous pieces have rank at most one and whose nonzero homogeneous elements are
units, is a twisted group algebra of the support of the grading. This file proves the
structure results used for Renard VI.4.4: the center is the sum of the pieces in the
radical of the commutation scalars, and `R` is free over its center with one monomial per
coset of the radical in the support.
-/

noncomputable section

open DirectSum

namespace Langlands.RankOneGraded

variable {ι k R : Type*} [AddCommGroup ι] [DecidableEq ι] [Field k] [Ring R] [Algebra k R]

/-- A grading whose homogeneous pieces have rank at most one and whose nonzero homogeneous
elements are units. -/
structure IsRankOneGrading (𝒜 : ι → Submodule k R) [GradedAlgebra 𝒜] : Prop where
  rank_le_one : ∀ i, Module.rank k (𝒜 i) ≤ 1
  isUnit_of_mem : ∀ i x, x ∈ 𝒜 i → x ≠ 0 → IsUnit x

variable {𝒜 : ι → Submodule k R} [GradedAlgebra 𝒜]

/-- An element all of whose homogeneous components vanish is zero. -/
theorem eq_zero_of_decompose {x : R} (h : ∀ i, (decompose 𝒜 x i : R) = 0) : x = 0 := by
  classical
  rw [← sum_support_decompose 𝒜 x]
  exact Finset.sum_eq_zero fun i _ => h i

/-- An element whose homogeneous components vanish away from `i` lies in `𝒜 i`. -/
theorem mem_of_decompose_eq_zero {x : R} {i : ι}
    (h : ∀ j, j ≠ i → (decompose 𝒜 x j : R) = 0) : x ∈ 𝒜 i := by
  classical
  rw [← sum_support_decompose 𝒜 x]
  refine Submodule.sum_mem _ fun j _ => ?_
  by_cases hj : j = i
  · subst hj
    exact (decompose 𝒜 x j).2
  · rw [h j hj]
    exact zero_mem _

/-- An element commuting with all homogeneous elements is central. -/
theorem mem_center_of_commute {x : R} (hx : ∀ i, ∀ y ∈ 𝒜 i, y * x = x * y) :
    x ∈ Subalgebra.center k R := by
  rw [Subalgebra.mem_center_iff]
  intro g
  induction g using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous m => exact hx _ m m.2
  | add a b ha hb => rw [add_mul, mul_add, ha, hb]


section Represent

/-! ### Linear actions on a vector space

A `k`-linear map `ρ : R →ₗ[k] End k M` that is multiplicative or anti-multiplicative; the
anti-multiplicative case covers right modules such as `Hom(I, π)` over `End(I)`. -/

variable {M : Type*} [AddCommGroup M] [Module k M] {ρ : R →ₗ[k] Module.End k M}

/-- `ρ` is multiplicative or anti-multiplicative. -/
def IsMulOrAntiMul (ρ : R →ₗ[k] Module.End k M) : Prop :=
  (∀ x y, ρ (x * y) = ρ x * ρ y) ∨ ∀ x y, ρ (x * y) = ρ y * ρ x

theorem trace_mul_eq (hρ : IsMulOrAntiMul ρ) (x y : R) :
    LinearMap.trace k M (ρ x * ρ y) = LinearMap.trace k M (ρ (x * y)) := by
  rcases hρ with h | h
  · rw [h]
  · rw [h, LinearMap.trace_mul_comm]

theorem trace_mul_comm (hρ : IsMulOrAntiMul ρ) (x y : R) :
    LinearMap.trace k M (ρ (x * y)) = LinearMap.trace k M (ρ (y * x)) := by
  rw [← trace_mul_eq hρ, ← trace_mul_eq hρ, LinearMap.trace_mul_comm]

theorem commute_of_mem_center (hρ : IsMulOrAntiMul ρ) {z : R}
    (hz : z ∈ Subalgebra.center k R) (x : R) : ρ x * ρ z = ρ z * ρ x := by
  have hzx := Subalgebra.mem_center_iff.mp hz x
  rcases hρ with h | h
  · rw [← h, ← h, hzx]
  · rw [← h, ← h, hzx]

/-- If `ρ` is surjective, central elements act by scalars. -/
theorem exists_eq_algebraMap_of_mem_center (hρ : IsMulOrAntiMul ρ)
    (hsurj : Function.Surjective ρ) {z : R} (hz : z ∈ Subalgebra.center k R) :
    ∃ c : k, ρ z = algebraMap k (Module.End k M) c := by
  refine (Algebra.IsCentral.mem_center_iff k).mp (Subalgebra.mem_center_iff.mpr fun X => ?_)
  obtain ⟨x, rfl⟩ := hsurj X
  exact commute_of_mem_center hρ hz x

theorem map_mul_of_eq_algebraMap (hρ : IsMulOrAntiMul ρ) {z : R} {c : k}
    (hc : ρ z = algebraMap k (Module.End k M) c) (x : R) : ρ (z * x) = c • ρ x := by
  rcases hρ with h | h
  · rw [h, hc, ← Algebra.smul_def]
  · rw [h, hc, ← Algebra.commutes, ← Algebra.smul_def]

theorem map_mul_eq_one (hρ : IsMulOrAntiMul ρ) {x y : R} (hx : ρ x = 1) (hy : ρ y = 1) :
    ρ (x * y) = 1 := by
  rcases hρ with h | h <;> rw [h, hx, hy, one_mul]

/-- **Burnside's theorem**: over an algebraically closed field, every linear endomorphism of a
finite-dimensional simple module is the action of an element of the algebra. -/
theorem exists_forall_eq_smul_of_isSimpleModule {A V : Type*} [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V] [IsSimpleModule A V]
    [FiniteDimensional k V] [IsAlgClosed k] (f : V →ₗ[k] V) : ∃ a : A, ∀ v, f v = a • v := by
  classical
  have hS := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := A) (V := V) k
  let F : Module.End (Module.End A V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun e v => by
        obtain ⟨c, rfl⟩ := hS.2 e
        simp only [Module.End.smul_def, Module.algebraMap_end_apply, RingHom.id_apply,
          map_smul] }
  let b := Module.finBasis k V
  obtain ⟨a, ha⟩ := jacobson_density F (Finset.univ.image b)
  refine ⟨a, fun v => ?_⟩
  rw [← b.sum_repr v, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_comm]
  congr 1
  exact ha _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))

/-- An algebra isomorphic to the group algebra of a finitely generated commutative group is
noetherian. -/
theorem isNoetherianRing_of_algEquiv_monoidAlgebra {Γ S : Type*} [CommGroup Γ] [Group.FG Γ]
    [CommRing S] [Algebra k S] (e : MonoidAlgebra k Γ ≃ₐ[k] S) : IsNoetherianRing S :=
  haveI := Algebra.FiniteType.isNoetherianRing k (MonoidAlgebra k Γ)
  isNoetherianRing_of_ringEquiv _ e.toRingEquiv

end Represent

namespace IsRankOneGrading

variable (h𝒜 : IsRankOneGrading 𝒜)
include h𝒜

/-- Every element of a piece is a scalar multiple of a given nonzero element. -/
theorem exists_smul_eq {i : ι} {u x : R} (hu : u ∈ 𝒜 i) (hu0 : u ≠ 0) (hx : x ∈ 𝒜 i) :
    ∃ c : k, c • u = x := by
  obtain ⟨v₀, hv₀⟩ := rank_le_one_iff.mp (h𝒜.rank_le_one i)
  obtain ⟨a, ha⟩ := hv₀ ⟨u, hu⟩
  obtain ⟨b, hb⟩ := hv₀ ⟨x, hx⟩
  have hu' : u = a • (v₀ : R) := by simpa using congrArg Subtype.val ha.symm
  have hx' : x = b • (v₀ : R) := by simpa using congrArg Subtype.val hb.symm
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hu0 (by simpa using hu')
  refine ⟨b / a, ?_⟩
  rw [hu', hx', smul_smul, div_mul_cancel₀ _ ha0]

/-- A product of nonzero homogeneous elements is nonzero. -/
theorem mul_ne_zero {i : ι} {u v : R} (hu : u ∈ 𝒜 i) (hu0 : u ≠ 0) (hv0 : v ≠ 0) :
    u * v ≠ 0 := fun h =>
  hv0 (((h𝒜.isUnit_of_mem i u hu hu0).mul_right_eq_zero).mp h)

/-- A nonzero homogeneous element of degree `i` has a two-sided inverse of degree `-i`. -/
theorem exists_inv_mem {i : ι} {u : R} (hu : u ∈ 𝒜 i) (hu0 : u ≠ 0) :
    ∃ v ∈ 𝒜 (-i), u * v = 1 ∧ v * u = 1 := by
  obtain ⟨U, rfl⟩ := h𝒜.isUnit_of_mem i u hu hu0
  refine ⟨(U⁻¹ : Rˣ), mem_of_decompose_eq_zero fun j hj => ?_, U.mul_inv, U.inv_mul⟩
  have h1 : (decompose 𝒜 ((U : R) * (U⁻¹ : Rˣ)) (i + j) : R) =
      (U : R) * decompose 𝒜 ((U⁻¹ : Rˣ) : R) j :=
    coe_decompose_mul_add_of_left_mem 𝒜 hu
  have hij : (0 : ι) ≠ i + j := by
    intro h
    apply hj
    rw [eq_neg_iff_add_eq_zero, add_comm, ← h]
  rw [U.mul_inv, decompose_of_mem_ne 𝒜 SetLike.GradedOne.one_mem hij] at h1
  have := congrArg (fun y => ((U⁻¹ : Rˣ) : R) * y) h1
  simpa [← mul_assoc] using this.symm

/-- Every element of the degree-zero piece is a scalar. -/
theorem exists_algebraMap_eq_of_mem_zero [Nontrivial R] {x : R} (hx : x ∈ 𝒜 0) :
    ∃ c : k, algebraMap k R c = x := by
  obtain ⟨c, hc⟩ := h𝒜.exists_smul_eq SetLike.GradedOne.one_mem one_ne_zero hx
  exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one, hc]⟩

omit h𝒜 in
/-- The homogeneous components of a central element are central. -/
theorem decompose_mem_center {x : R} (hx : x ∈ Subalgebra.center k R) (i : ι) :
    (decompose 𝒜 x i : R) ∈ Subalgebra.center k R := by
  refine mem_center_of_commute (𝒜 := 𝒜) fun j y hy => ?_
  have h1 : (decompose 𝒜 (y * x) (j + i) : R) = y * decompose 𝒜 x i :=
    coe_decompose_mul_add_of_left_mem 𝒜 hy
  have h2 : (decompose 𝒜 (x * y) (i + j) : R) = decompose 𝒜 x i * y :=
    coe_decompose_mul_add_of_right_mem 𝒜 hy
  rw [← h1, ← h2, (Subalgebra.mem_center_iff.mp hx y), add_comm]

variable [Nontrivial R]

/-- The support of the grading: the degrees with a nonzero piece. -/
def support : AddSubgroup ι where
  carrier := {i | 𝒜 i ≠ ⊥}
  zero_mem' := (Submodule.ne_bot_iff _).mpr ⟨1, SetLike.GradedOne.one_mem, one_ne_zero⟩
  add_mem' := by
    intro i j hi hj
    obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp hi
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hj
    exact (Submodule.ne_bot_iff _).mpr
      ⟨u * v, SetLike.mul_mem_graded hu hv, h𝒜.mul_ne_zero hu hu0 hv0⟩
  neg_mem' := by
    intro i hi
    obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp hi
    obtain ⟨v, hv, huv, -⟩ := h𝒜.exists_inv_mem hu hu0
    refine (Submodule.ne_bot_iff _).mpr ⟨v, hv, ?_⟩
    rintro rfl
    simp at huv

theorem mem_support_iff {i : ι} : i ∈ h𝒜.support ↔ ∃ x ∈ 𝒜 i, x ≠ 0 :=
  Submodule.ne_bot_iff _

/-- The radical of the grading: the degrees in the support whose piece is central. -/
def radical : AddSubgroup ι where
  carrier := {i | 𝒜 i ≠ ⊥ ∧ ∀ x ∈ 𝒜 i, x ∈ Subalgebra.center k R}
  zero_mem' := by
    refine ⟨h𝒜.support.zero_mem, fun x hx => ?_⟩
    obtain ⟨c, rfl⟩ := h𝒜.exists_algebraMap_eq_of_mem_zero hx
    exact Subalgebra.algebraMap_mem _ c
  add_mem' := by
    rintro i j ⟨hi, hi'⟩ ⟨hj, hj'⟩
    obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp hi
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hj
    refine ⟨h𝒜.support.add_mem hi hj, fun x hx => ?_⟩
    obtain ⟨c, rfl⟩ := h𝒜.exists_smul_eq (SetLike.mul_mem_graded hu hv)
      (h𝒜.mul_ne_zero hu hu0 hv0) hx
    exact Subalgebra.smul_mem _ (Subalgebra.mul_mem _ (hi' u hu) (hj' v hv)) c
  neg_mem' := by
    rintro i ⟨hi, hi'⟩
    obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp hi
    obtain ⟨v, hv, huv, hvu⟩ := h𝒜.exists_inv_mem hu hu0
    have hv0 : v ≠ 0 := by
      rintro rfl
      simp at huv
    refine ⟨h𝒜.support.neg_mem hi, fun x hx => ?_⟩
    obtain ⟨c, rfl⟩ := h𝒜.exists_smul_eq hv hv0 hx
    refine Subalgebra.smul_mem _ ?_ c
    rw [Subalgebra.mem_center_iff]
    intro y
    have hc := Subalgebra.mem_center_iff.mp (hi' u hu) y
    calc y * v = v * u * (y * v) := by rw [hvu, one_mul]
      _ = v * (y * u) * v := by rw [hc]; noncomm_ring
      _ = v * y := by rw [mul_assoc, mul_assoc, huv, mul_one]

theorem radical_le_support : h𝒜.radical ≤ h𝒜.support := fun _ hi => hi.1

/-- A nonzero central element of degree `i` forces `i` into the radical. -/
theorem mem_radical_of_mem_center {i : ι} {x : R} (hx : x ∈ 𝒜 i) (hx0 : x ≠ 0)
    (hxc : x ∈ Subalgebra.center k R) : i ∈ h𝒜.radical := by
  refine ⟨(Submodule.ne_bot_iff _).mpr ⟨x, hx, hx0⟩, fun y hy => ?_⟩
  obtain ⟨c, rfl⟩ := h𝒜.exists_smul_eq hx hx0 hy
  exact Subalgebra.smul_mem _ hxc c

/-- An element is central if and only if its homogeneous components vanish away from the
radical. -/
theorem mem_center_iff {x : R} :
    x ∈ Subalgebra.center k R ↔ ∀ i, i ∉ h𝒜.radical → (decompose 𝒜 x i : R) = 0 := by
  classical
  constructor
  · intro hx i hi
    by_contra h0
    exact hi (h𝒜.mem_radical_of_mem_center (decompose 𝒜 x i).2 h0
      (decompose_mem_center (𝒜 := 𝒜) hx i))
  · intro h
    rw [← sum_support_decompose 𝒜 x]
    refine Subalgebra.sum_mem _ fun i _ => ?_
    by_cases hi : i ∈ h𝒜.radical
    · exact hi.2 _ (decompose 𝒜 x i).2
    · rw [h i hi]
      exact Subalgebra.zero_mem _

/-- A nonzero homogeneous element of degree outside the radical fails to commute with some
nonzero homogeneous element, up to a scalar different from one. -/
theorem exists_mul_eq_smul_mul {i : ι} {w : R} (hw : w ∈ 𝒜 i) (hw0 : w ≠ 0)
    (hi : i ∉ h𝒜.radical) :
    ∃ j, ∃ v ∈ 𝒜 j, v ≠ 0 ∧ ∃ c : k, c ≠ 1 ∧ w * v = c • (v * w) := by
  have hwc : w ∉ Subalgebra.center k R := fun hc =>
    hi (h𝒜.mem_radical_of_mem_center hw hw0 hc)
  have : ¬ ∀ j, ∀ y ∈ 𝒜 j, y * w = w * y := fun h => hwc (mem_center_of_commute h)
  push Not at this
  obtain ⟨j, v, hv, hvw⟩ := this
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp at hvw
  have hvw' : v * w ∈ 𝒜 (i + j) := by
    rw [add_comm]
    exact SetLike.mul_mem_graded hv hw
  obtain ⟨c, hc⟩ := h𝒜.exists_smul_eq hvw' (h𝒜.mul_ne_zero hv hv0 hw0)
    (SetLike.mul_mem_graded hw hv)
  refine ⟨j, v, hv, hv0, c, ?_, hc.symm⟩
  rintro rfl
  rw [one_smul] at hc
  exact hvw hc


/-- The cosets of the radical in the support. -/
abbrev Cosets : Type _ := h𝒜.support ⧸ h𝒜.radical.addSubgroupOf h𝒜.support

/-- The chosen representative degree of a coset of the radical in the support. -/
def rep (q : h𝒜.Cosets) : ι := (Quotient.out q : h𝒜.support)

theorem rep_mem_support (q : h𝒜.Cosets) : h𝒜.rep q ∈ h𝒜.support :=
  (Quotient.out q : h𝒜.support).2

/-- Two cosets whose representatives differ by an element of the radical are equal. -/
theorem eq_of_rep_sub_mem {p q : h𝒜.Cosets} (h : h𝒜.rep p - h𝒜.rep q ∈ h𝒜.radical) :
    p = q := by
  rw [← QuotientAddGroup.out_eq' p, ← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq,
    AddSubgroup.mem_addSubgroupOf]
  have := h𝒜.radical.neg_mem h
  simpa [rep, neg_sub, sub_eq_neg_add] using this

/-- An element of the support differs from the representative of its coset by an element
of the radical. -/
theorem sub_rep_mem (i : h𝒜.support) :
    (i : ι) - h𝒜.rep (QuotientAddGroup.mk i) ∈ h𝒜.radical := by
  have h := QuotientAddGroup.out_eq' (QuotientAddGroup.mk i : h𝒜.Cosets)
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h
  simpa [rep, neg_add_eq_sub] using h

/-- The chosen nonzero monomial of a coset. -/
def mono (q : h𝒜.Cosets) : R :=
  ((h𝒜.mem_support_iff).mp (h𝒜.rep_mem_support q)).choose

theorem mono_mem (q : h𝒜.Cosets) : h𝒜.mono q ∈ 𝒜 (h𝒜.rep q) :=
  ((h𝒜.mem_support_iff).mp (h𝒜.rep_mem_support q)).choose_spec.1

theorem mono_ne_zero (q : h𝒜.Cosets) : h𝒜.mono q ≠ 0 :=
  ((h𝒜.mem_support_iff).mp (h𝒜.rep_mem_support q)).choose_spec.2

/-- The chosen inverse of the monomial of a coset. -/
def monoInv (q : h𝒜.Cosets) : R :=
  (h𝒜.exists_inv_mem (h𝒜.mono_mem q) (h𝒜.mono_ne_zero q)).choose

theorem monoInv_mem (q : h𝒜.Cosets) : h𝒜.monoInv q ∈ 𝒜 (-h𝒜.rep q) :=
  (h𝒜.exists_inv_mem (h𝒜.mono_mem q) (h𝒜.mono_ne_zero q)).choose_spec.1

theorem mono_mul_monoInv (q : h𝒜.Cosets) : h𝒜.mono q * h𝒜.monoInv q = 1 :=
  (h𝒜.exists_inv_mem (h𝒜.mono_mem q) (h𝒜.mono_ne_zero q)).choose_spec.2.1

theorem monoInv_mul_mono (q : h𝒜.Cosets) : h𝒜.monoInv q * h𝒜.mono q = 1 :=
  (h𝒜.exists_inv_mem (h𝒜.mono_mem q) (h𝒜.mono_ne_zero q)).choose_spec.2.2

theorem decompose_mul_mono (x : R) (q : h𝒜.Cosets) (d : ι) :
    (decompose 𝒜 (x * h𝒜.mono q) d : R) = decompose 𝒜 x (d - h𝒜.rep q) * h𝒜.mono q := by
  have := coe_decompose_mul_add_of_right_mem 𝒜 (a := x) (i := d - h𝒜.rep q) (h𝒜.mono_mem q)
  rwa [sub_add_cancel] at this

omit h𝒜 [Nontrivial R] in
theorem smul_def (z : Subalgebra.center k R) (x : R) : z • x = (z : R) * x := rfl

/-- The monomials are linearly independent over the center. -/
theorem linearIndependent_mono : LinearIndependent (Subalgebra.center k R) h𝒜.mono := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum p hp
  apply Subtype.ext
  refine eq_zero_of_decompose (𝒜 := 𝒜) fun a => ?_
  by_cases ha : a ∈ h𝒜.radical
  · have h0 := congrArg (GradedAlgebra.proj 𝒜 (a + h𝒜.rep p)) hsum
    rw [map_sum, map_zero] at h0
    simp only [GradedAlgebra.proj_apply, smul_def, h𝒜.decompose_mul_mono] at h0
    rw [Finset.sum_eq_single p] at h0
    · rw [add_sub_cancel_right] at h0
      exact ((h𝒜.isUnit_of_mem _ _ (h𝒜.mono_mem p) (h𝒜.mono_ne_zero p)).mul_left_eq_zero).mp h0
    · intro q _ hqp
      rw [(h𝒜.mem_center_iff).mp (g q).2 _ ?_, zero_mul]
      intro hmem
      apply hqp
      refine (h𝒜.eq_of_rep_sub_mem ?_).symm
      have := h𝒜.radical.sub_mem hmem ha
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    · intro hp'
      exact absurd hp hp'
  · exact (h𝒜.mem_center_iff).mp (g p).2 a ha

/-- The monomials span the algebra over its center. -/
theorem span_mono :
    ⊤ ≤ Submodule.span (Subalgebra.center k R) (Set.range h𝒜.mono) := by
  rintro x -
  induction x using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => exact Submodule.zero_mem _
  | add a b ha hb => exact Submodule.add_mem _ ha hb
  | @homogeneous i m =>
    by_cases hm : (m : R) = 0
    · rw [hm]
      exact Submodule.zero_mem _
    have hi : i ∈ h𝒜.support := (h𝒜.mem_support_iff).mpr ⟨m, m.2, hm⟩
    set q : h𝒜.Cosets := QuotientAddGroup.mk ⟨i, hi⟩
    have hmem : (m : R) * h𝒜.monoInv q ∈ 𝒜 (i - h𝒜.rep q) := by
      rw [sub_eq_add_neg]
      exact SetLike.mul_mem_graded m.2 (h𝒜.monoInv_mem q)
    have hc : (m : R) * h𝒜.monoInv q ∈ Subalgebra.center k R :=
      (h𝒜.sub_rep_mem ⟨i, hi⟩).2 _ hmem
    have : (m : R) = (⟨_, hc⟩ : Subalgebra.center k R) • h𝒜.mono q := by
      rw [smul_def, mul_assoc, h𝒜.monoInv_mul_mono, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)

/-- The algebra is free over its center, with one monomial per coset of the radical in the
support. -/
def basis : Module.Basis h𝒜.Cosets (Subalgebra.center k R) R :=
  Module.Basis.mk h𝒜.linearIndependent_mono h𝒜.span_mono

@[simp]
theorem basis_apply (q : h𝒜.Cosets) : h𝒜.basis q = h𝒜.mono q :=
  Module.Basis.mk_apply _ _ _


section Count

variable {M : Type*} [AddCommGroup M] [Module k M] {ρ : R →ₗ[k] Module.End k M}

/-- A homogeneous element of degree outside the radical acts with trace zero. -/
theorem trace_eq_zero_of_not_mem_radical (hρ : IsMulOrAntiMul ρ) {i : ι} {w : R}
    (hw : w ∈ 𝒜 i) (hi : i ∉ h𝒜.radical) : LinearMap.trace k M (ρ w) = 0 := by
  by_cases hw0 : w = 0
  · rw [hw0, map_zero, map_zero]
  obtain ⟨j, v, hv, hv0, c, hc1, hc⟩ := h𝒜.exists_mul_eq_smul_mul hw hw0 hi
  obtain ⟨v', -, hvv', hv'v⟩ := h𝒜.exists_inv_mem hv hv0
  have hw' : w = c • (v * (w * v')) := by
    calc w = w * v * v' := by rw [mul_assoc, hvv', mul_one]
      _ = c • (v * (w * v')) := by rw [hc, smul_mul_assoc, mul_assoc]
  have htr : LinearMap.trace k M (ρ w) = c * LinearMap.trace k M (ρ w) := by
    conv_lhs => rw [hw']
    rw [map_smul, map_smul, trace_mul_comm hρ, mul_assoc, hv'v, mul_one, smul_eq_mul]
  have : (1 - c) * LinearMap.trace k M (ρ w) = 0 := by rw [sub_mul, one_mul, ← htr, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hc1.symm)

/-- The images of the monomials are linearly independent. -/
theorem linearIndependent_map_mono [CharZero k] [FiniteDimensional k M] [Nontrivial M]
    (hρ1 : ρ 1 = 1) (hρ : IsMulOrAntiMul ρ) :
    LinearIndependent k fun q => ρ (h𝒜.mono q) := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum p hp
  have h0 := congrArg (fun X => LinearMap.trace k M (X * ρ (h𝒜.monoInv p))) hsum
  simp only [Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, zero_mul, map_zero,
    trace_mul_eq hρ, smul_eq_mul] at h0
  rw [Finset.sum_eq_single p, h𝒜.mono_mul_monoInv, hρ1, LinearMap.trace_one] at h0
  · exact (mul_eq_zero.mp h0).resolve_right (Nat.cast_ne_zero.mpr Module.finrank_pos.ne')
  · intro q _ hqp
    rw [h𝒜.trace_eq_zero_of_not_mem_radical hρ
      (SetLike.mul_mem_graded (h𝒜.mono_mem q) (h𝒜.monoInv_mem p)), mul_zero]
    intro hmem
    exact hqp (h𝒜.eq_of_rep_sub_mem (by simpa [sub_eq_add_neg] using hmem))
  · intro hp'
    exact absurd hp hp'

/-- If `ρ` is surjective, the images of the monomials span `End k M`. -/
theorem map_mem_span_map_mono (hρ : IsMulOrAntiMul ρ) (hsurj : Function.Surjective ρ) (x : R) :
    ρ x ∈ Submodule.span k (Set.range fun q => ρ (h𝒜.mono q)) := by
  have hx := h𝒜.span_mono (Submodule.mem_top (x := x))
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨q, rfl⟩ := hy
    exact Submodule.subset_span ⟨q, rfl⟩
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    rw [map_add]
    exact Submodule.add_mem _ hy hz
  | smul z y _ hy =>
    obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_mem_center hρ hsurj z.2
    rw [smul_def, map_mul_of_eq_algebraMap hρ hc]
    exact Submodule.smul_mem _ c hy

/-- **Counting the cosets.** If `R` acts on a nonzero finite-dimensional vector space `M` over a
field of characteristic zero, multiplicatively or anti-multiplicatively, with every linear
endomorphism of `M` in the image, then the radical has finite index in the support, equal to
`(dim M)²`. -/
theorem finite_cosets_and_card_eq [CharZero k] [FiniteDimensional k M] [Nontrivial M]
    (hρ1 : ρ 1 = 1) (hρ : IsMulOrAntiMul ρ) (hsurj : Function.Surjective ρ) :
    Finite h𝒜.Cosets ∧ Nat.card h𝒜.Cosets = Module.finrank k M ^ 2 := by
  have hli := h𝒜.linearIndependent_map_mono hρ1 hρ
  have hfin : Finite h𝒜.Cosets := hli.finite
  refine ⟨hfin, ?_⟩
  let b : Module.Basis h𝒜.Cosets k (Module.End k M) :=
    Module.Basis.mk hli fun X _ => by
      obtain ⟨x, rfl⟩ := hsurj X
      exact h𝒜.map_mem_span_map_mono hρ hsurj x
  rw [← Module.finrank_eq_nat_card_basis b, Module.finrank_linearMap, sq]

end Count


section Center

variable {M : Type*} [AddCommGroup M] [Module k M] [Nontrivial M] {ρ : R →ₗ[k] Module.End k M}

/-- Every degree in the radical carries an element acting as the identity. -/
theorem exists_mem_map_eq_one (hρ1 : ρ 1 = 1) (hρ : IsMulOrAntiMul ρ)
    (hsurj : Function.Surjective ρ) {a : ι} (ha : a ∈ h𝒜.radical) : ∃ x ∈ 𝒜 a, ρ x = 1 := by
  obtain ⟨u, hu, hu0⟩ := (h𝒜.mem_support_iff).mp (h𝒜.radical_le_support ha)
  obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_mem_center hρ hsurj (ha.2 u hu)
  obtain ⟨v, -, huv, -⟩ := h𝒜.exists_inv_mem hu hu0
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    have h0 : ρ (u * v) = 0 := by
      rcases hρ with h | h <;> simp [h, hc]
    rw [huv, hρ1] at h0
    exact one_ne_zero h0
  refine ⟨c⁻¹ • u, Submodule.smul_mem _ _ hu, ?_⟩
  rw [map_smul, hc, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hc0, map_one]

omit [Nontrivial R] in
/-- In each degree, at most one element acts as the identity. -/
theorem eq_of_map_eq_one {a : ι} {x y : R} (hx : x ∈ 𝒜 a) (hy : y ∈ 𝒜 a) (hx1 : ρ x = 1)
    (hy1 : ρ y = 1) : x = y := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx1
    exact zero_ne_one hx1
  obtain ⟨c, rfl⟩ := h𝒜.exists_smul_eq hx hx0 hy
  rw [map_smul, hx1] at hy1
  have : c = 1 := by
    apply (algebraMap k (Module.End k M)).injective
    rw [Algebra.algebraMap_eq_smul_one, hy1, map_one]
  rw [this, one_smul]

/-- **The center is a group algebra.** If `R` acts on a nonzero vector space `M`,
multiplicatively or anti-multiplicatively, with every linear endomorphism of `M` in the image,
then the center of `R` is isomorphic to the group algebra of the radical, the class of `a` going
to the element of degree `a` acting as the identity on `M`. -/
theorem exists_algEquiv_center (hρ1 : ρ 1 = 1) (hρ : IsMulOrAntiMul ρ)
    (hsurj : Function.Surjective ρ) :
    ∃ e : MonoidAlgebra k (Multiplicative h𝒜.radical) ≃ₐ[k] Subalgebra.center k R,
      ∀ a : Multiplicative h𝒜.radical,
        (e (MonoidAlgebra.of k _ a) : R) ∈ 𝒜 (a.toAdd : ι) ∧
          ρ (e (MonoidAlgebra.of k _ a)) = 1 := by
  classical
  choose u hu hu1 using fun a : Multiplicative h𝒜.radical =>
    h𝒜.exists_mem_map_eq_one hρ1 hρ hsurj a.toAdd.2
  have huc : ∀ a, u a ∈ Subalgebra.center k R := fun a => a.toAdd.2.2 _ (hu a)
  have hu0 : ∀ a, u a ≠ 0 := fun a h => by
    have := hu1 a
    rw [h, map_zero] at this
    exact zero_ne_one this
  let ψ : Multiplicative h𝒜.radical →* Subalgebra.center k R :=
    { toFun := fun a => ⟨u a, huc a⟩
      map_one' := Subtype.ext (h𝒜.eq_of_map_eq_one (hu 1) SetLike.GradedOne.one_mem (hu1 1) hρ1)
      map_mul' := fun a b => Subtype.ext (h𝒜.eq_of_map_eq_one (hu (a * b))
        (SetLike.mul_mem_graded (hu a) (hu b)) (hu1 _) (map_mul_eq_one hρ (hu1 a) (hu1 b))) }
  let L := MonoidAlgebra.lift k (Subalgebra.center k R) (Multiplicative h𝒜.radical) ψ
  have hL : ∀ a, L (MonoidAlgebra.of k _ a) = ⟨u a, huc a⟩ := fun a =>
    MonoidAlgebra.lift_of _ _
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    rw [← MonoidAlgebra.coeff_eq_zero]
    ext b
    have h0 := congrArg
      (fun z => GradedAlgebra.proj 𝒜 (b.toAdd : ι) ((Subalgebra.center k R).val z)) hf
    simp only [L, MonoidAlgebra.lift_apply, Finsupp.sum, map_sum, map_smul, map_zero,
      Subalgebra.coe_val, GradedAlgebra.proj_apply] at h0
    rw [Finset.sum_eq_single b] at h0
    · have h1 : (decompose 𝒜 (u b) (b.toAdd : ι) : R) = u b := decompose_of_mem_same 𝒜 (hu b)
      change f.coeff b • (decompose 𝒜 (u b) (b.toAdd : ι) : R) = 0 at h0
      rw [h1, smul_eq_zero] at h0
      exact h0.resolve_right (hu0 b)
    · intro a _ hab
      have hne : (a.toAdd : ι) ≠ b.toAdd := fun h => hab (Subtype.ext h)
      change f.coeff a • (decompose 𝒜 (u a) (b.toAdd : ι) : R) = 0
      rw [decompose_of_mem_ne 𝒜 (hu a) hne, smul_zero]
    · intro hb
      rw [Finsupp.notMem_support_iff.mp hb, zero_smul]
  have hsurj' : Function.Surjective L := by
    intro z
    have hz : (z : R) ∈ ((Subalgebra.center k R).val.comp L).range := by
      rw [← sum_support_decompose 𝒜 (z : R)]
      refine Subalgebra.sum_mem _ fun i _ => ?_
      by_cases hi : i ∈ h𝒜.radical
      · obtain ⟨c, hc⟩ := h𝒜.exists_smul_eq (hu (Multiplicative.ofAdd ⟨i, hi⟩)) (hu0 _)
          (decompose 𝒜 (z : R) i).2
        refine ⟨MonoidAlgebra.single (Multiplicative.ofAdd ⟨i, hi⟩) c, ?_⟩
        change ((L (MonoidAlgebra.single (Multiplicative.ofAdd ⟨i, hi⟩) c) :
          Subalgebra.center k R) : R) = _
        simp only [L, MonoidAlgebra.lift_single]
        rw [← hc]
        rfl
      · rw [(h𝒜.mem_center_iff).mp z.2 i hi]
        exact Subalgebra.zero_mem _
    obtain ⟨f, hf⟩ := hz
    exact ⟨f, Subtype.ext hf⟩
  refine ⟨AlgEquiv.ofBijective L (show Function.Bijective L from ⟨hinj, hsurj'⟩), fun a => ?_⟩
  change (L _ : R) ∈ _ ∧ ρ (L _ : R) = 1
  rw [hL]
  exact ⟨hu a, hu1 a⟩

end Center

section Noetherian

/-- If the radical has finite index in the support and the center is noetherian, then the
algebra is left and right noetherian. -/
theorem isNoetherianRing_of_finite [Finite h𝒜.Cosets]
    [IsNoetherianRing (Subalgebra.center k R)] :
    IsNoetherianRing R ∧ IsNoetherianRing Rᵐᵒᵖ := by
  have := Fintype.ofFinite h𝒜.Cosets
  have : Module.Finite (Subalgebra.center k R) R := Module.Finite.of_basis h𝒜.basis
  have hN : IsNoetherian (Subalgebra.center k R) R :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  refine ⟨isNoetherian_of_tower (Subalgebra.center k R) hN, ?_⟩
  have : IsScalarTower (Subalgebra.center k R) Rᵐᵒᵖ Rᵐᵒᵖ := ⟨fun z a b => by
    apply MulOpposite.unop_injective
    simp only [smul_eq_mul, MulOpposite.unop_mul, MulOpposite.unop_smul, smul_def]
    rw [← mul_assoc, ← mul_assoc, Subalgebra.mem_center_iff.mp z.2]⟩
  have hN' : IsNoetherian (Subalgebra.center k R) Rᵐᵒᵖ :=
    isNoetherian_of_linearEquiv (MulOpposite.opLinearEquiv (Subalgebra.center k R))
  exact isNoetherian_of_tower (Subalgebra.center k R) hN'

end Noetherian

end IsRankOneGrading

end Langlands.RankOneGraded
