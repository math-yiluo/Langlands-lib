import Langlands.CommutativeAlgebra.GradedFormallySmoothPolynomial
import Mathlib.Data.Fin.Tuple.Sort

/-! # Weight-graded formally smooth algebras with positive heights are polynomial algebras -/

noncomputable section

open MvPolynomial Finsupp

namespace Langlands.Algebra.WeightGradedFormallySmooth

section Height

variable {σ Λ : Type*} [AddCommMonoid Λ] (h : Λ →+ ℤ)

/-- The height of the weight of a monomial is its weight for the heights of the variables. -/
theorem height_weight (w : σ → Λ) (m : σ →₀ ℕ) :
    h (weight w m) = weight (fun j => h (w j)) m := by
  rw [weight_apply, weight_apply, map_finsuppSum]
  simp only [map_nsmul]

variable {h}

/-- A monomial of weight zero is constant when all variables have positive height. -/
theorem eq_zero_of_weight_eq_zero {w : σ → Λ} (hw : ∀ j, 0 < h (w j)) {m : σ →₀ ℕ}
    (hm : h (weight w m) = 0) : m = 0 := by
  by_contra hm0
  obtain ⟨j, hj⟩ : ∃ j, m j ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hm0 (Finsupp.ext hc)
  have h1 := le_weight_of_ne_zero (w := fun j => h (w j)) (fun s => (hw s).le) hj
  rw [← height_weight, hm] at h1
  exact absurd (hw j) (not_lt.2 h1)

/-- A variable occurring in a monomial other than itself has smaller height than the monomial,
when all variables have positive height. -/
theorem height_lt_of_ne_single {w : σ → Λ} (hw : ∀ j, 0 < h (w j)) {m : σ →₀ ℕ} {i : σ}
    (hi : m i ≠ 0) (hne : m ≠ single i 1) : h (w i) < h (weight w m) := by
  have h1 := weight_sub_single_add (w := fun j => h (w j)) hi
  rw [← height_weight h w m] at h1
  have h2 : m - single i 1 ≠ 0 := by
    intro h0
    apply hne
    rw [← sub_add_single_one_cancel hi, h0, zero_add]
  have h3 : 0 < weight (fun j => h (w j)) (m - single i 1) := by
    obtain ⟨j, hj⟩ : ∃ j, (m - Finsupp.single i 1 : σ →₀ ℕ) j ≠ 0 := by
      by_contra hc
      push Not at hc
      exact h2 (Finsupp.ext hc)
    exact (hw j).trans_le (le_weight_of_ne_zero (w := fun j => h (w j)) (fun s => (hw s).le) hj)
  omega

/-- A monomial containing `X i` whose weight is that of `X i` is `X i`, when all variables have
positive height. -/
theorem eq_single_of_weight_eq {w : σ → Λ} (hw : ∀ j, 0 < h (w j)) {m : σ →₀ ℕ} {i : σ}
    (hi : m i ≠ 0) (hm : weight w m = w i) : m = single i 1 := by
  by_contra hne
  have := height_lt_of_ne_single hw hi hne
  rw [hm] at this
  exact lt_irrefl _ this

end Height

section Components

variable {k C σ Λ : Type*} [CommRing k] [CommRing C] [Algebra k C] [AddCommMonoid Λ]
  [DecidableEq Λ] (𝒜 : Λ → Submodule k C) [GradedAlgebra 𝒜]

/-- Evaluation at homogeneous elements carries weighted homogeneous components to graded
components. -/
theorem decompose_aeval {w : σ → Λ} {y : σ → C} (hy : ∀ j, y j ∈ 𝒜 (w j))
    (f : MvPolynomial σ k) (χ : Λ) :
    (DirectSum.decompose 𝒜 (aeval y f) χ : C) =
      aeval y (weightedHomogeneousComponent w χ f) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial m a =>
    have hm : aeval y (monomial m a) ∈ 𝒜 (weight w m) := by
      rw [aeval_monomial, ← Algebra.smul_def, weight_apply]
      exact Submodule.smul_mem _ a
        (SetLike.prod_pow_mem_graded 𝒜 w y m (fun j _ => hy j))
    have hmon := isWeightedHomogeneous_monomial (R := k) w m a rfl
    by_cases hd : weight w m = χ
    · subst hd
      rw [hmon.weightedHomogeneousComponent_same, DirectSum.decompose_of_mem_same _ hm]
    · rw [hmon.weightedHomogeneousComponent_ne χ (Ne.symm hd),
        DirectSum.decompose_of_mem_ne _ hm hd, map_zero]
  | add p q hp hq =>
    rw [map_add, DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add, hp, hq,
      map_add, map_add]

/-- If evaluation at homogeneous elements is injective, a polynomial whose value is homogeneous
of weight `χ` is weighted homogeneous of weight `χ`. -/
theorem isWeightedHomogeneous_of_aeval_mem {w : σ → Λ} {y : σ → C} (hy : ∀ j, y j ∈ 𝒜 (w j))
    (hinj : Function.Injective (aeval y : MvPolynomial σ k →ₐ[k] C)) {f : MvPolynomial σ k}
    {χ : Λ} (hf : aeval y f ∈ 𝒜 χ) : IsWeightedHomogeneous w f χ := by
  have h := decompose_aeval 𝒜 hy f χ
  rw [DirectSum.decompose_of_mem_same 𝒜 hf] at h
  rw [hinj h]
  exact weightedHomogeneousComponent_isWeightedHomogeneous χ f

end Components

section Relations

variable {k C σ Λ : Type*} [Field k] [CommRing C] [Algebra k C] [AddCommMonoid Λ]
  [DecidableEq Λ] (𝒜 : Λ → Submodule k C) [GradedAlgebra 𝒜] {h : Λ →+ ℤ}
  {w : σ → Λ} {y : σ → C}

/-- With positive heights, the weight-zero component of a polynomial is its constant term. -/
theorem weightedHomogeneousComponent_zero_eq (hw : ∀ j, 0 < h (w j))
    (f : MvPolynomial σ k) : weightedHomogeneousComponent w 0 f = MvPolynomial.C (f.coeff 0) := by
  classical
  ext m
  rw [coeff_weightedHomogeneousComponent, coeff_C]
  by_cases hm : m = 0
  · subst hm
    simp
  · rw [ite_eq_right (fun h0 => hm (eq_zero_of_weight_eq_zero hw (by rw [h0, map_zero]))),
      ite_eq_right (Ne.symm hm)]

/-- A relation among homogeneous elements of positive height has no constant term. -/
theorem coeff_zero_eq_zero [Nontrivial C] (hw : ∀ j, 0 < h (w j)) (hy : ∀ j, y j ∈ 𝒜 (w j))
    {f : MvPolynomial σ k} (hf : aeval y f = 0) : f.coeff 0 = 0 := by
  have h0 := decompose_aeval 𝒜 hy f 0
  rw [hf, weightedHomogeneousComponent_zero_eq hw, aeval_C] at h0
  apply (algebraMap k C).injective
  rw [← h0, (algebraMap k C).map_zero, DirectSum.decompose_zero, DirectSum.zero_apply,
    ZeroMemClass.coe_zero]

/-- If a relation among homogeneous elements of positive height has a nonzero linear
coefficient at `i`, then `y i` lies in the subalgebra generated by the other `y j`. -/
theorem mem_adjoin_of_coeff_single_ne_zero (hw : ∀ j, 0 < h (w j)) (hy : ∀ j, y j ∈ 𝒜 (w j))
    {f : MvPolynomial σ k} (hf : aeval y f = 0) {i : σ} (hi : f.coeff (single i 1) ≠ 0) :
    y i ∈ Algebra.adjoin k (y '' {j | j ≠ i}) := by
  classical
  set f₀ := weightedHomogeneousComponent w (w i) f with hf₀
  set c := f.coeff (single i 1) with hc_def
  have h0 : aeval y f₀ = 0 := by
    rw [hf₀, ← decompose_aeval 𝒜 hy, hf]
    simp
  have hc : f₀.coeff (single i 1) = c := by
    rw [hf₀, coeff_weightedHomogeneousComponent, ite_eq_left (by simp [weight_single])]
  set g := f₀ - monomial (single i 1) c with hg_def
  have hg : aeval y g ∈ Algebra.adjoin k (y '' {j | j ≠ i}) := by
    rw [g.as_sum, map_sum]
    refine Subalgebra.sum_mem _ fun m hm => ?_
    have hmem : ∀ j ∈ m.support, y j ∈ Algebra.adjoin k (y '' {j | j ≠ i}) := by
      intro j hj
      refine Algebra.subset_adjoin (Set.mem_image_of_mem y ?_)
      intro hji
      subst hji
      rw [MvPolynomial.mem_support_iff] at hm
      rw [Finsupp.mem_support_iff] at hj
      have hm' : m ≠ single j 1 := by
        rintro rfl
        apply hm
        rw [hg_def, coeff_sub, coeff_monomial, ite_eq_left rfl, hc, sub_self]
      rw [hg_def, coeff_sub, coeff_monomial, ite_eq_right (Ne.symm hm'), sub_zero] at hm
      have hwm : weight w m = w j :=
        weightedHomogeneousComponent_isWeightedHomogeneous (w j) f hm
      exact hm' (eq_single_of_weight_eq hw hj hwm)
    rw [aeval_monomial]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.prod_mem _ fun j hj => Subalgebra.pow_mem _ (hmem j hj) _)
  have key : aeval y f₀ = aeval y g + algebraMap k C c * y i := by
    rw [hg_def, map_sub, aeval_monomial, Finsupp.prod_single_index (by simp), pow_one]
    ring
  rw [h0] at key
  have hyi : y i = algebraMap k C c⁻¹ * -aeval y g := by
    calc y i = algebraMap k C c⁻¹ * (algebraMap k C c * y i) := by
          rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hi, map_one, one_mul]
      _ = algebraMap k C c⁻¹ * -aeval y g := by
          rw [eq_neg_of_add_eq_zero_right key.symm]
  rw [hyi]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (neg_mem hg)

end Relations

section Generators

variable {k C Λ : Type*} [Field k] [CommRing C] [Algebra k C] [AddCommMonoid Λ]
  [DecidableEq Λ] (𝒜 : Λ → Submodule k C) [GradedAlgebra 𝒜] (h : Λ →+ ℤ)

/-- `C` is generated as a `k`-algebra by `N` homogeneous elements of positive height. -/
def HasWeightGenerators (N : ℕ) : Prop :=
  ∃ (w : Fin N → Λ) (y : Fin N → C), (∀ i, 0 < h (w i)) ∧ (∀ i, y i ∈ 𝒜 (w i)) ∧
    Algebra.adjoin k (Set.range y) = ⊤

/-- A finitely generated graded algebra whose weight-zero part is `k`, and whose other nonzero
homogeneous elements have positive height, is generated by finitely many homogeneous elements
of positive height. -/
theorem exists_hasWeightGenerators [Algebra.FiniteType k C]
    (h0 : 𝒜 0 = LinearMap.range (Algebra.linearMap k C))
    (hpos : ∀ χ, χ ≠ 0 → ∀ a ∈ 𝒜 χ, a ≠ 0 → 0 < h χ) :
    ∃ N, HasWeightGenerators 𝒜 h N := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := k) (A := C)
  let ι := Σ c : s, ((DirectSum.decompose 𝒜 c.1).support.filter (· ≠ 0))
  let e : ι → Λ := fun p => p.2.1
  let y : ι → C := fun p => DirectSum.decompose 𝒜 p.1.1 p.2.1
  have hy : ∀ p, y p ∈ 𝒜 (e p) := fun p => (DirectSum.decompose 𝒜 _ _).2
  have he : ∀ p, 0 < h (e p) := by
    intro p
    have hp := Finset.mem_filter.1 p.2.2
    refine hpos (e p) hp.2 (y p) (hy p) ?_
    intro hzero
    apply DFinsupp.mem_support_iff.1 hp.1
    exact Subtype.ext hzero
  refine ⟨Fintype.card ι, e ∘ (Fintype.equivFin ι).symm, y ∘ (Fintype.equivFin ι).symm,
    fun i => he _, fun i => hy _, ?_⟩
  rw [EquivLike.range_comp, ← top_le_iff, ← hs, Algebra.adjoin_le_iff]
  intro c hc
  rw [← DirectSum.sum_support_decompose 𝒜 c]
  refine Subalgebra.sum_mem _ fun d hd => ?_
  by_cases hd0 : d = 0
  · subst hd0
    obtain ⟨a, ha⟩ : (DirectSum.decompose 𝒜 c 0 : C) ∈
        LinearMap.range (Algebra.linearMap k C) := h0 ▸ (DirectSum.decompose 𝒜 c 0).2
    rw [← ha]
    exact Subalgebra.algebraMap_mem _ a
  · exact Algebra.subset_adjoin ⟨⟨⟨c, hc⟩, ⟨d, Finset.mem_filter.2 ⟨hd, hd0⟩⟩⟩, rfl⟩

variable [Nontrivial C]

/-- For a generating family of homogeneous elements of positive height of minimal length,
every relation lies in the square of the ideal of variables. -/
theorem mem_pow_two_of_minimal {N : ℕ} {w : Fin N → Λ} {y : Fin N → C}
    (hw : ∀ i, 0 < h (w i)) (hy : ∀ i, y i ∈ 𝒜 (w i))
    (hgen : Algebra.adjoin k (Set.range y) = ⊤)
    (hmin : ∀ M < N, ¬ HasWeightGenerators 𝒜 h M) {f : MvPolynomial (Fin N) k}
    (hf : aeval y f = 0) : f ∈ idealOfVars (Fin N) k ^ 2 := by
  rw [mem_pow_idealOfVars_iff']
  intro m hm
  by_cases hm0 : m = 0
  · subst hm0
    exact coeff_zero_eq_zero 𝒜 hw hy hf
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hm0 (Finsupp.ext hc)
  have hmi : m = single i 1 := by
    refine Langlands.Algebra.GradedFormallySmooth.eq_single_of_weight_le (w := fun _ => 1)
      (fun _ => Nat.one_pos) hi ?_
    rw [← degree_eq_weight_one]
    omega
  subst hmi
  by_contra hc
  have hyi := mem_adjoin_of_coeff_single_ne_zero 𝒜 hw hy hf hc
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by have := i.pos; omega⟩
  refine hmin M (Nat.lt_succ_self M) ⟨w ∘ i.succAbove, y ∘ i.succAbove, fun j => hw _,
    fun j => hy _, ?_⟩
  rw [← top_le_iff, ← hgen, Algebra.adjoin_le_iff]
  rintro _ ⟨j, rfl⟩
  by_cases hj : j = i
  · subst hj
    refine Algebra.adjoin_mono ?_ hyi
    rintro _ ⟨l, hl, rfl⟩
    obtain ⟨z, rfl⟩ := Fin.exists_succAbove_eq hl
    exact ⟨z, rfl⟩
  · obtain ⟨z, rfl⟩ := Fin.exists_succAbove_eq hj
    exact Algebra.subset_adjoin ⟨z, rfl⟩

/-- **Weight-graded polynomial coordinates.** A finitely generated, formally smooth algebra
over a field `k`, graded by an additive monoid `Λ` with a height `h : Λ →+ ℤ`, whose
weight-zero part is `k` and whose other nonzero homogeneous elements have positive height, is a
polynomial algebra on finitely many homogeneous generators of positive height. The generators
can be listed in order of nondecreasing height. -/
theorem exists_weight_aeval_bijective [Algebra.FiniteType k C] [Algebra.FormallySmooth k C]
    (h0 : 𝒜 0 = LinearMap.range (Algebra.linearMap k C))
    (hpos : ∀ χ, χ ≠ 0 → ∀ a ∈ 𝒜 χ, a ≠ 0 → 0 < h χ) :
    ∃ (n : ℕ) (w : Fin n → Λ) (x : Fin n → C), (∀ i, 0 < h (w i)) ∧
      Monotone (fun i => h (w i)) ∧ (∀ i, x i ∈ 𝒜 (w i)) ∧
      Function.Bijective (MvPolynomial.aeval x : MvPolynomial (Fin n) k →ₐ[k] C) := by
  classical
  have hex := exists_hasWeightGenerators 𝒜 h h0 hpos
  obtain ⟨w, y, hw, hy, hgen⟩ := Nat.find_spec hex
  have hsurj : Function.Surjective
      (aeval y : MvPolynomial (Fin (Nat.find hex)) k →ₐ[k] C) := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval]
    exact hgen
  have hbij : Function.Bijective
      (aeval y : MvPolynomial (Fin (Nat.find hex)) k →ₐ[k] C) :=
    ⟨Langlands.Algebra.GradedFormallySmooth.aeval_injective_of_ker_le hsurj fun f hf =>
      mem_pow_two_of_minimal 𝒜 h hw hy hgen (fun M hM => Nat.find_min hex hM)
        (RingHom.mem_ker.1 hf), hsurj⟩
  let τ := Tuple.sort (fun i => h (w i))
  refine ⟨Nat.find hex, w ∘ τ, y ∘ τ, fun i => hw _,
    Tuple.monotone_sort (fun i => h (w i)), fun i => hy _, ?_⟩
  have hcomp : (aeval (y ∘ τ) : MvPolynomial (Fin (Nat.find hex)) k →ₐ[k] C) =
      (aeval y).comp (renameEquiv k τ).toAlgHom := by
    refine MvPolynomial.algHom_ext fun i => ?_
    simp [renameEquiv]
  rw [hcomp, AlgHom.coe_comp]
  exact hbij.comp (renameEquiv k τ).bijective

end Generators

end Langlands.Algebra.WeightGradedFormallySmooth
