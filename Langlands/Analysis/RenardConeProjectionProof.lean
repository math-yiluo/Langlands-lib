import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Langlands.Analysis.RenardConeProjectionStatements

/-! # Projection on a cone in a Euclidean space (Renard V.5.5): proof

Proof of `Langlands.Renard.ConeProjectionStatements`. The nearest point and the obtuse-angle
characterization come from Mathlib's projection on complete convex sets; characterization (iii)
uses that the closure of `Č` is the dual cone of `C` when `C ≠ E`. The Corollary projects on the
closed cone `{x | ∀ i, 0 ≤ ⟨αᵢ, x⟩}`, which is the closure of `C`.
-/

namespace Langlands.Renard

universe u v

open scoped BigOperators
open Filter Topology

namespace ConeProjection

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For a convex set `K` and `v₀ ∈ K`, being a nearest point of `K` to `v` is equivalent to the
obtuse-angle inequality. -/
theorem nearest_iff_inner_le_zero {K : Set E} (hK : Convex ℝ K) {v v₀ : E} (hv₀ : v₀ ∈ K) :
    (∀ w ∈ K, ‖v - v₀‖ ≤ ‖v - w‖) ↔ ∀ w ∈ K, inner ℝ (v - v₀) (w - v₀) ≤ 0 := by
  have hbdd : BddBelow (Set.range fun w : K => ‖v - w‖) :=
    ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩
  have : Nonempty K := ⟨⟨v₀, hv₀⟩⟩
  rw [← norm_eq_iInf_iff_real_inner_le_zero hK hv₀]
  constructor
  · intro h
    exact le_antisymm (le_ciInf fun w => h w w.2) (ciInf_le hbdd ⟨v₀, hv₀⟩)
  · intro h w hw
    rw [h]
    exact ciInf_le hbdd ⟨w, hw⟩

/-- At most one point of `K` satisfies the obtuse-angle inequality. -/
theorem eq_of_inner_le_zero {K : Set E} {v v₀ v₁ : E} (h₀ : v₀ ∈ K) (h₁ : v₁ ∈ K)
    (H₀ : ∀ w ∈ K, inner ℝ (v - v₀) (w - v₀) ≤ 0)
    (H₁ : ∀ w ∈ K, inner ℝ (v - v₁) (w - v₁) ≤ 0) : v₀ = v₁ := by
  have a := H₀ v₁ h₁
  have b := H₁ v₀ h₀
  have e : v₀ - v₁ = -(v₁ - v₀) := (neg_sub v₁ v₀).symm
  rw [e, inner_neg_right] at b
  have hle : inner ℝ (v₁ - v₀) (v₁ - v₀) ≤ 0 := by
    have : inner ℝ (v₁ - v₀) (v₁ - v₀) =
        inner ℝ (v - v₀) (v₁ - v₀) - inner ℝ (v - v₁) (v₁ - v₀) := by
      rw [← inner_sub_left]
      congr 1
      abel
    rw [this]
    linarith
  exact (sub_eq_zero.1 (real_inner_self_nonpos.1 hle)).symm

/-- A nonempty closed convex set of a finite-dimensional space contains a point satisfying the
obtuse-angle inequality. -/
theorem exists_inner_le_zero [FiniteDimensional ℝ E] {K : Set E} (hne : K.Nonempty)
    (hcl : IsClosed K) (hK : Convex ℝ K) (v : E) :
    ∃ v₀ ∈ K, ∀ w ∈ K, inner ℝ (v - v₀) (w - v₀) ≤ 0 := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨v₀, hv₀, h⟩ := exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hK v
  exact ⟨v₀, hv₀, (norm_eq_iInf_iff_real_inner_le_zero hK hv₀).1 h⟩

/-- If `⟨u, w⟩ ≥ 0` for `u ∈ A`, `w ∈ B`, the same holds on the closures. -/
theorem inner_nonneg_of_mem_closure {A B : Set E} (hAB : ∀ u ∈ A, ∀ w ∈ B, 0 ≤ inner ℝ u w)
    {u w : E} (hu : u ∈ closure A) (hw : w ∈ closure B) : 0 ≤ inner ℝ u w := by
  have hS : IsClosed {p : E × E | 0 ≤ inner ℝ p.1 p.2} :=
    isClosed_le continuous_const (continuous_fst.inner continuous_snd)
  have hsub : closure (A ×ˢ B) ⊆ {p : E × E | 0 ≤ inner ℝ p.1 p.2} :=
    closure_minimal (fun p hp => hAB p.1 hp.1 p.2 hp.2) hS
  rw [closure_prod_eq] at hsub
  exact hsub (Set.mk_mem_prod hu hw)

/-- `x` is the limit of `x + ε • y` as `ε → 0⁺`. -/
theorem tendsto_add_smul (x y : E) :
    Tendsto (fun ε : ℝ => x + ε • y) (𝓝[>] 0) (𝓝 x) := by
  have h : Tendsto (fun ε : ℝ => x + ε • y) (𝓝 0) (𝓝 (x + (0 : ℝ) • y)) :=
    (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
  rw [zero_smul, add_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- A point of an open set can be moved a little in any direction without leaving it. -/
theorem exists_pos_add_smul_mem {C : Set E} (hC : IsOpen C) {a : E} (ha : a ∈ C) (y : E) :
    ∃ ε : ℝ, 0 < ε ∧ a + ε • y ∈ C := by
  obtain ⟨ε, hεC, hεpos⟩ :=
    (((tendsto_add_smul a y).eventually (hC.mem_nhds ha)).and
      (eventually_mem_nhdsWithin (s := Set.Ioi 0))).exists
  exact ⟨ε, hεpos, hεC⟩

/-- For an open set `C`, a nonzero vector with nonnegative pairings on `C` has positive
pairings on `C`. -/
theorem inner_pos_of_inner_nonneg {C : Set E} (hopen : IsOpen C) {u : E} (hu0 : u ≠ 0)
    (hu : ∀ w ∈ C, 0 ≤ inner ℝ u w) : ∀ w ∈ C, 0 < inner ℝ u w := by
  intro w hw
  obtain ⟨ε, hε, hεC⟩ := exists_pos_add_smul_mem hopen hw (-u)
  have h := hu _ hεC
  rw [inner_add_right, real_inner_smul_right, inner_neg_right] at h
  have hpos : 0 < inner ℝ u u := real_inner_self_pos.2 hu0
  nlinarith

variable {C : Set E} (hcone : ∀ t : ℝ, 0 < t → ∀ x ∈ C, t • x ∈ C)
include hcone

/-- The closure of a nonempty cone contains `0`. -/
theorem zero_mem_closure (hne : C.Nonempty) : (0 : E) ∈ closure C := by
  obtain ⟨x, hx⟩ := hne
  have h := tendsto_add_smul (0 : E) x
  simp only [zero_add] at h
  exact mem_closure_of_tendsto h (eventually_nhdsWithin_of_forall fun t ht => hcone t ht x hx)

/-- The closure of a nonempty cone is stable under nonnegative scalars. -/
theorem smul_mem_closure (hne : C.Nonempty) {t : ℝ} (ht : 0 ≤ t) {x : E}
    (hx : x ∈ closure C) : t • x ∈ closure C := by
  rcases ht.eq_or_lt with rfl | ht
  · rw [zero_smul]
    exact zero_mem_closure hcone hne
  · exact map_mem_closure (continuous_const_smul t) hx fun y hy => hcone t ht y hy

/-- For a nonempty convex open cone `C ≠ E`, some vector has positive pairings on `C`. -/
theorem exists_inner_pos [FiniteDimensional ℝ E] (hopen : IsOpen C) (hconv : Convex ℝ C)
    (hne : C.Nonempty) (hC : C ≠ Set.univ) : ∃ u : E, ∀ w ∈ C, 0 < inner ℝ u w := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem C).1 hC
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hconv hopen hx
  set z : E := (InnerProductSpace.toDual ℝ E).symm f with hz
  have hzf : ∀ y, inner ℝ z y = f y := fun y => InnerProductSpace.toDual_symm_apply
  have hfa : ∀ a ∈ C, f a ≤ 0 := by
    intro a ha
    by_contra hpos'
    have hpos : 0 < f a := lt_of_not_ge hpos'
    have ht : 0 < |f x| / f a + 1 := by
      have := div_nonneg (abs_nonneg (f x)) hpos.le
      linarith
    have h := hf _ (hcone _ ht a ha)
    rw [map_smul, smul_eq_mul, add_mul, div_mul_cancel₀ _ hpos.ne', one_mul] at h
    linarith [le_abs_self (f x)]
  refine ⟨-z, inner_pos_of_inner_nonneg hopen ?_ ?_⟩
  · intro hz0
    obtain ⟨a, ha⟩ := hne
    have h := hf a ha
    rw [← hzf, ← hzf, neg_eq_zero.1 hz0, inner_zero_left, inner_zero_left] at h
    exact lt_irrefl _ h
  · intro w hw
    rw [inner_neg_left, hzf]
    linarith [hfa w hw]

/-- For a nonempty convex open cone `C ≠ E`, the dual cone `{u | ∀ w ∈ C, 0 ≤ ⟨u, w⟩}` lies in
the closure of `Č = {u | ∀ w ∈ C, 0 < ⟨u, w⟩}`. -/
theorem mem_closure_dual [FiniteDimensional ℝ E] (hopen : IsOpen C) (hconv : Convex ℝ C)
    (hne : C.Nonempty) (hC : C ≠ Set.univ) {u : E} (hu : ∀ w ∈ C, 0 ≤ inner ℝ u w) :
    u ∈ closure {u : E | ∀ w ∈ C, 0 < inner ℝ u w} := by
  obtain ⟨u₁, hu₁⟩ := exists_inner_pos hcone hopen hconv hne hC
  refine mem_closure_of_tendsto (tendsto_add_smul u u₁)
    (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => ?_)
  intro w hw
  rw [inner_add_left, real_inner_smul_left]
  exact add_pos_of_nonneg_of_pos (hu w hw) (mul_pos hε (hu₁ w hw))

end General

section Basis

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (α : Module.Basis ι ℝ E) {ω : ι → E}
  (hαω : ∀ i j : ι, inner ℝ (α i) (ω j) = if i = j then 1 else 0)

omit [DecidableEq ι] in
/-- A vector orthogonal to every member of a basis is zero. -/
theorem eq_zero_of_inner_basis {y : E} (hy : ∀ k, inner ℝ (α k) y = 0) : y = 0 := by
  have h : inner ℝ y y = 0 := by
    calc inner ℝ y y = inner ℝ (∑ i, α.repr y i • α i) y := by rw [α.sum_repr]
      _ = 0 := by
          simp only [sum_inner, real_inner_smul_left, hy, mul_zero, Finset.sum_const_zero]
  exact inner_self_eq_zero.1 h

include hαω

/-- The `α`-pairings of `∑ tᵢ ωᵢ` are the coefficients `tᵢ`. -/
theorem inner_basis_sum (t : ι → ℝ) (k : ι) : inner ℝ (α k) (∑ i, t i • ω i) = t k := by
  simp [inner_sum, real_inner_smul_right, hαω]

/-- Expansion in the dual family `ω`, with coefficients the pairings with `α`. -/
theorem eq_sum_dual (x : E) : x = ∑ i, inner ℝ (α i) x • ω i := by
  refine (sub_eq_zero.1 (eq_zero_of_inner_basis α fun k => ?_))
  rw [inner_sub_right, inner_basis_sum α hαω, sub_self]

/-- Expansion in the basis `α`, with coefficients the pairings with `ω`. -/
theorem eq_sum_basis (x : E) : x = ∑ j, inner ℝ x (ω j) • α j := by
  have hrepr : ∀ j, α.repr x j = inner ℝ x (ω j) := by
    intro j
    conv_rhs => rw [← α.sum_repr x]
    simp only [sum_inner, real_inner_smul_left, hαω, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  conv_lhs => rw [← α.sum_repr x]
  simp only [hrepr]

omit hαω in
/-- A sum over the complement of `F` as a sum over all indices. -/
theorem sum_compl_eq (F : Finset ι) (t : ι → ℝ) (f : ι → E) :
    ∑ i ∈ Finset.univ \ F, t i • f i = ∑ i, (if i ∈ F then 0 else t i) • f i := by
  symm
  rw [← Finset.sum_sdiff (Finset.subset_univ F)]
  have h0 : ∑ i ∈ F, (if i ∈ F then 0 else t i) • f i = 0 :=
    Finset.sum_eq_zero fun i hi => by simp [hi]
  rw [h0, add_zero]
  exact Finset.sum_congr rfl fun i hi => by simp [(Finset.mem_sdiff.1 hi).2]

omit hαω in
/-- A sum over `F` as a sum over all indices. -/
theorem sum_mem_eq (F : Finset ι) (s : ι → ℝ) (f : ι → E) :
    ∑ j ∈ F, s j • f j = ∑ j, (if j ∈ F then s j else 0) • f j := by
  symm
  rw [← Finset.sum_sdiff (Finset.subset_univ F)]
  have h0 : ∑ j ∈ Finset.univ \ F, (if j ∈ F then s j else 0) • f j = 0 :=
    Finset.sum_eq_zero fun j hj => by simp [(Finset.mem_sdiff.1 hj).2]
  rw [h0, zero_add]
  exact Finset.sum_congr rfl fun j hj => by simp [hj]

/-- The pairing of `αₖ` with `∑_{i ∉ F} tᵢ ωᵢ`. -/
theorem inner_basis_sum_compl (F : Finset ι) (t : ι → ℝ) (k : ι) :
    inner ℝ (α k) (∑ i ∈ Finset.univ \ F, t i • ω i) = if k ∈ F then 0 else t k := by
  rw [sum_compl_eq, inner_basis_sum α hαω]

/-- The closed cone `{x | ∀ i, 0 ≤ ⟨αᵢ, x⟩}` is the closure of `{∑ tᵢ ωᵢ | tᵢ > 0}`. -/
theorem closure_cone_eq :
    closure {x : E | ∃ t : ι → ℝ, (∀ i, 0 < t i) ∧ x = ∑ i, t i • ω i} =
      {x : E | ∀ i, 0 ≤ inner ℝ (α i) x} := by
  refine Set.Subset.antisymm ?_ ?_
  · refine closure_minimal ?_ ?_
    · rintro x ⟨t, ht, rfl⟩ i
      rw [inner_basis_sum α hαω]
      exact (ht i).le
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_const.inner continuous_id)
  · intro x hx
    refine mem_closure_of_tendsto (tendsto_add_smul x (∑ i, ω i))
      (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => ?_)
    refine ⟨fun i => inner ℝ (α i) x + ε, fun i => add_pos_of_nonneg_of_pos (hx i) hε, ?_⟩
    simp only [add_smul, Finset.sum_add_distrib, Finset.smul_sum]
    rw [← eq_sum_dual α hαω x]

omit [Fintype ι] [DecidableEq ι] hαω in
/-- The closed cone `{x | ∀ i, 0 ≤ ⟨αᵢ, x⟩}` is convex. -/
theorem convex_nonneg_cone : Convex ℝ {x : E | ∀ i, 0 ≤ inner ℝ (α i) x} := by
  intro x hx y hy a b ha hb _ i
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))

/-- For a decomposition `v = ∑_{i ∉ F} tᵢ ωᵢ - ∑_{j ∈ F} sⱼ αⱼ`, the vector
`∑_{i ∉ F} tᵢ ωᵢ` lies in the closed cone and satisfies the obtuse-angle inequality there. -/
theorem decomposition_inner_le_zero (F : Finset ι) (t s : ι → ℝ)
    (ht : ∀ i ∈ Finset.univ \ F, 0 < t i) (hs : ∀ j ∈ F, 0 ≤ s j) {v : E}
    (hv : v = (∑ i ∈ Finset.univ \ F, t i • ω i) - ∑ j ∈ F, s j • α j) :
    (∑ i ∈ Finset.univ \ F, t i • ω i) ∈ {x : E | ∀ i, 0 ≤ inner ℝ (α i) x} ∧
      ∀ w ∈ {x : E | ∀ i, 0 ≤ inner ℝ (α i) x},
        inner ℝ (v - ∑ i ∈ Finset.univ \ F, t i • ω i) (w - ∑ i ∈ Finset.univ \ F, t i • ω i)
          ≤ 0 := by
  set p := ∑ i ∈ Finset.univ \ F, t i • ω i with hp
  have hpk : ∀ k, inner ℝ (α k) p = if k ∈ F then 0 else t k :=
    inner_basis_sum_compl α hαω F t
  have hq : ∀ x : E, inner ℝ (∑ j ∈ F, s j • α j) x
      = ∑ j, (if j ∈ F then s j else 0) * inner ℝ (α j) x := by
    intro x
    rw [sum_mem_eq, sum_inner]
    simp only [real_inner_smul_left]
  refine ⟨fun k => ?_, fun w hw => ?_⟩
  · rw [hpk]
    split_ifs with hk
    · exact le_rfl
    · exact (ht k (Finset.mem_sdiff.2 ⟨Finset.mem_univ k, hk⟩)).le
  · have hvp : v - p = -(∑ j ∈ F, s j • α j) := by rw [hv]; abel
    rw [hvp, inner_neg_left, inner_sub_right, hq, hq]
    have hqp : ∑ j, (if j ∈ F then s j else 0) * inner ℝ (α j) p = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hpk]
      split_ifs <;> simp
    have hqw : 0 ≤ ∑ j, (if j ∈ F then s j else 0) * inner ℝ (α j) w := by
      refine Finset.sum_nonneg fun j _ => mul_nonneg ?_ (hw j)
      split_ifs with hj
      · exact hs j hj
      · exact le_rfl
    rw [hqp, sub_zero]
    linarith

/-- The finite set `F` is read off from `∑_{i ∉ F} tᵢ ωᵢ`: it is where the `α`-pairings
vanish. -/
theorem mem_iff_inner_eq_zero (F : Finset ι) (t : ι → ℝ) (ht : ∀ i ∈ Finset.univ \ F, 0 < t i)
    (k : ι) : k ∈ F ↔ inner ℝ (α k) (∑ i ∈ Finset.univ \ F, t i • ω i) = 0 := by
  rw [inner_basis_sum_compl α hαω]
  by_cases hk : k ∈ F
  · simp [hk]
  · simp only [hk, ite_false, false_iff]
    exact (ht k (Finset.mem_sdiff.2 ⟨Finset.mem_univ k, hk⟩)).ne'

end Basis

end ConeProjection

open ConeProjection

/-- Renard V.5.5, Proposition. -/
theorem coneProjectionStatement : ConeProjectionStatement.{v} := by
  intro E _ _ _ C hopen hconv hne hcone Cdual v
  have hKconv : Convex ℝ (closure C) := hconv.closure
  have hiff : ∀ v₀ ∈ closure C, ((∀ w ∈ closure C, ‖v - v₀‖ ≤ ‖v - w‖) ↔
      ∀ w ∈ closure C, inner ℝ (v - v₀) (w - v₀) ≤ 0) :=
    fun v₀ hv₀ => nearest_iff_inner_le_zero hKconv hv₀
  refine ⟨?_, fun v₀ hv₀ => ⟨hiff v₀ hv₀, fun hC => ?_⟩⟩
  · obtain ⟨v₀, hv₀, h⟩ := exists_inner_le_zero hne.closure isClosed_closure hKconv v
    refine ⟨v₀, ⟨hv₀, (hiff v₀ hv₀).2 h⟩, fun v₁ hv₁ => ?_⟩
    exact eq_of_inner_le_zero hv₁.1 hv₀ ((hiff v₁ hv₁.1).1 hv₁.2) h
  · rw [hiff v₀ hv₀]
    constructor
    · intro h
      have h0 := h 0 (zero_mem_closure hcone hne)
      have h2 := h ((2 : ℝ) • v₀) (smul_mem_closure hcone hne (by norm_num) hv₀)
      have e2 : (2 : ℝ) • v₀ - v₀ = v₀ := by rw [two_smul, add_sub_cancel_right]
      rw [e2] at h2
      rw [zero_sub, inner_neg_right] at h0
      have horth : inner ℝ (v - v₀) v₀ = 0 := by linarith
      refine ⟨mem_closure_dual hcone hopen hconv hne hC fun w hw => ?_, horth⟩
      have := h w (subset_closure hw)
      rw [inner_sub_right, horth, sub_zero] at this
      rw [← neg_sub, inner_neg_left]
      linarith
    · rintro ⟨hmem, horth⟩ w hw
      have h := inner_nonneg_of_mem_closure (A := Cdual) (B := C)
        (fun u hu w hw => (hu w hw).le) hmem hw
      rw [inner_sub_right, horth, sub_zero, ← neg_sub, inner_neg_left]
      linarith

/-- Renard V.5.5, Corollary. -/
theorem coneProjectionBasisStatement : ConeProjectionBasisStatement.{u, v} := by
  intro ι _ _ E _ _ _ α ω hαω C v
  set K : Set E := {x : E | ∀ i, 0 ≤ inner ℝ (α i) x} with hK
  have hclos : closure C = K := closure_cone_eq α hαω
  have hKconv : Convex ℝ K := convex_nonneg_cone α
  -- Part 2: a decomposition gives the nearest point.
  have hpart2 : ∀ (F : Finset ι) (t s : ι → ℝ),
      (∀ i ∈ Finset.univ \ F, 0 < t i) → (∀ j ∈ F, 0 ≤ s j) →
      v = (∑ i ∈ Finset.univ \ F, t i • ω i) - ∑ j ∈ F, s j • α j →
        (∑ i ∈ Finset.univ \ F, t i • ω i) ∈ closure C ∧
          ∀ w ∈ closure C, ‖v - ∑ i ∈ Finset.univ \ F, t i • ω i‖ ≤ ‖v - w‖ := by
    intro F t s ht hs hv
    obtain ⟨hpK, hineq⟩ := decomposition_inner_le_zero α hαω F t s ht hs hv
    rw [hclos]
    exact ⟨hpK, (nearest_iff_inner_le_zero hKconv hpK).2 hineq⟩
  refine ⟨?_, hpart2⟩
  -- Part 1: existence and uniqueness of `F`.
  have hKcl : IsClosed K := by
    rw [← hclos]
    exact isClosed_closure
  have hKne : K.Nonempty := ⟨0, by intro i; simp⟩
  obtain ⟨v₀, hv₀, h⟩ := exists_inner_le_zero hKne hKcl hKconv v
  set a : ι → ℝ := fun i => inner ℝ (α i) v₀ with ha
  set b : ι → ℝ := fun j => inner ℝ (v₀ - v) (ω j) with hb
  have ha0 : ∀ i, 0 ≤ a i := hv₀
  have hb0 : ∀ j, 0 ≤ b j := by
    intro j
    have hw : v₀ + ω j ∈ K := by
      intro i
      rw [inner_add_right, hαω]
      have := hv₀ i
      split_ifs <;> linarith
    have := h _ hw
    rw [add_sub_cancel_left] at this
    show 0 ≤ inner ℝ (v₀ - v) (ω j)
    rw [← neg_sub, inner_neg_left]
    linarith
  have horth : inner ℝ (v₀ - v) v₀ = 0 := by
    have h0 := h 0 (by intro i; simp)
    have h2 := h ((2 : ℝ) • v₀) (by
      intro i
      rw [real_inner_smul_right]
      exact mul_nonneg (by norm_num) (hv₀ i))
    have e2 : (2 : ℝ) • v₀ - v₀ = v₀ := by rw [two_smul, add_sub_cancel_right]
    rw [e2] at h2
    rw [zero_sub, inner_neg_right] at h0
    rw [← neg_sub, inner_neg_left]
    linarith
  have hab : ∀ i, a i * b i = 0 := by
    have hsum : inner ℝ (v₀ - v) v₀ = ∑ i, a i * b i := by
      have e := congrArg (inner ℝ (v₀ - v)) (eq_sum_dual α hαω v₀)
      rw [inner_sum] at e
      simp only [real_inner_smul_right] at e
      exact e
    rw [horth] at hsum
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_nonneg (ha0 j) (hb0 j)).1 hsum.symm i
      (Finset.mem_univ i)
  set F : Finset ι := Finset.univ.filter fun i => a i = 0 with hF
  have hmemF : ∀ i, i ∈ F ↔ a i = 0 := fun i => by simp [hF]
  have hpos : ∀ i ∈ Finset.univ \ F, 0 < a i := by
    intro i hi
    have hi' := (Finset.mem_sdiff.1 hi).2
    rw [hmemF] at hi'
    exact lt_of_le_of_ne (ha0 i) (Ne.symm hi')
  have hdecomp : v = (∑ i ∈ Finset.univ \ F, a i • ω i) - ∑ j ∈ F, b j • α j := by
    have e1 : ∑ i ∈ Finset.univ \ F, a i • ω i = v₀ := by
      rw [sum_compl_eq]
      conv_rhs => rw [eq_sum_dual α hαω v₀]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with hi
      · show (0 : ℝ) • ω i = a i • ω i
        rw [(hmemF i).1 hi]
      · rfl
    have e2 : ∑ j ∈ F, b j • α j = v₀ - v := by
      rw [sum_mem_eq]
      conv_rhs => rw [eq_sum_basis α hαω (v₀ - v)]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs with hj
      · rfl
      · have hbj : b j = 0 := by
          have := hab j
          rw [mul_eq_zero] at this
          exact this.resolve_left (fun h' => hj ((hmemF j).2 h'))
        show (0 : ℝ) • α j = b j • α j
        rw [hbj]
    rw [e1, e2, sub_sub_cancel]
  refine ⟨F, ⟨a, b, hpos, fun j _ => hb0 j, hdecomp⟩, ?_⟩
  rintro G ⟨t, s, ht, hs, hv⟩
  obtain ⟨hpG, hineqG⟩ := decomposition_inner_le_zero α hαω G t s ht hs hv
  obtain ⟨hpF, hineqF⟩ := decomposition_inner_le_zero α hαω F a b hpos (fun j _ => hb0 j) hdecomp
  have heq := eq_of_inner_le_zero hpG hpF hineqG hineqF
  ext k
  rw [mem_iff_inner_eq_zero α hαω G t ht, mem_iff_inner_eq_zero α hαω F a hpos, heq]

/-- Renard V.5.5: the Proposition and the Corollary. -/
theorem coneProjectionStatements : ConeProjectionStatements.{u, v} :=
  ⟨coneProjectionStatement, coneProjectionBasisStatement⟩

end Langlands.Renard
