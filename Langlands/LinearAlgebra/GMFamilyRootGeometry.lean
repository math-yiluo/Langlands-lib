import Langlands.LinearAlgebra.GMFamiliesRoots
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic

/-! # Root geometry for `(G, M)`-families -/

noncomputable section

open scoped RealInnerProductSpace
open Classical

namespace Langlands.GMFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Linearly independent vectors can be tested against any prescribed real values. -/
theorem exists_inner_values {ι : Type*} {v : ι → E} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) : ∃ h : E, ∀ i, ⟪v i, h⟫ = b i := by
  let B := Module.Basis.span hv
  obtain ⟨f, hf⟩ := (B.constr ℝ b).exists_extend
  let l : StrongDual ℝ E := f.toContinuousLinearMap
  refine ⟨(InnerProductSpace.toDual ℝ E).symm l, fun i => ?_⟩
  rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
  change f (v i) = b i
  have h := LinearMap.congr_fun hf (B i)
  simpa only [B, LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.coe_span_apply,
    Module.Basis.constr_basis] using h

section PositiveVectors

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The indecomposable members of a finite positive set. -/
private def indecomposables (S : Finset V) : Finset V :=
  S.filter fun v => ¬ ∃ u ∈ S, ∃ w ∈ S, v = u + w

private theorem card_lt_filter_of_lt (S : Finset V) (f : Module.Dual ℝ V)
    {u v : V} (hu : u ∈ S) (hlt : f u < f v) :
    (S.filter fun w => f w < f u).card < (S.filter fun w => f w < f v).card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro w hw
    obtain ⟨hw, hwu⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨hw, hwu.trans hlt⟩
  · intro h
    have hy : u ∈ S.filter (fun w => f w < f v) := Finset.mem_filter.mpr ⟨hu, hlt⟩
    rw [← h] at hy
    exact (lt_irrefl _) (Finset.mem_filter.mp hy).2

/-- A strictly positive grading ensures that every member of a finite set is a sum of its
indecomposable members, with natural-number multiplicities. -/
private theorem exists_sum_indecomposables (S : Finset V) (f : Module.Dual ℝ V)
    (hf : ∀ x ∈ S, 0 < f x) {x : V} (hx : x ∈ S) :
    ∃ c : indecomposables S → ℕ, ∑ i, c i • (i : V) = x := by
  let height (v : V) := (S.filter fun w => f w < f v).card
  revert hx
  induction x using (measure height).wf.induction with
  | h x ih =>
    intro hx
    by_cases hi : x ∈ indecomposables S
    · let i : indecomposables S := ⟨x, hi⟩
      refine ⟨fun j => if j = i then 1 else 0, ?_⟩
      simp [ite_smul, i]
    · have hdec : ∃ u ∈ S, ∃ v ∈ S, x = u + v := by
        simpa [indecomposables, hx] using hi
      obtain ⟨u, hu, v, hv, rfl⟩ := hdec
      have hfu : f u < f (u + v) := by rw [map_add]; exact lt_add_of_pos_right _ (hf v hv)
      have hfv : f v < f (u + v) := by rw [map_add]; exact lt_add_of_pos_left _ (hf u hu)
      obtain ⟨c, hc⟩ := ih u (card_lt_filter_of_lt S f hu hfu) hu
      obtain ⟨d, hd⟩ := ih v (card_lt_filter_of_lt S f hv hfv) hv
      exact ⟨fun i => c i + d i, by simp only [add_nsmul, Finset.sum_add_distrib, hc, hd]⟩

end PositiveVectors

variable {R : Finset E}

omit [FiniteDimensional ℝ E] in
/-- Distinct roots with positive pairing have a difference in the root set. -/
theorem IsRootSet.sub_mem_of_inner_pos (hR : IsRootSet R) {α β : E}
    (hα : α ∈ R) (hβ : β ∈ R) (hne : α ≠ β) (hpos : 0 < ⟪α, β⟫) : α - β ∈ R := by
  have hα₀ : (0 : ℝ) < ⟪α, α⟫ := real_inner_self_pos.mpr (fun h => hR.1 (h ▸ hα))
  have hβ₀ : (0 : ℝ) < ⟪β, β⟫ := real_inner_self_pos.mpr (fun h => hR.1 (h ▸ hβ))
  have hsym : ⟪β, α⟫ = ⟪α, β⟫ := real_inner_comm _ _
  obtain ⟨m, hm⟩ := hR.2.2 β hβ α hα
  obtain ⟨n, hn⟩ := hR.2.2 α hα β hβ
  have hmpos : 0 < m := by
    have h : (0 : ℝ) < (m : ℝ) := by rw [← hm]; exact div_pos (mul_pos two_pos hpos) hβ₀
    exact_mod_cast h
  have hnpos : 0 < n := by
    have h : (0 : ℝ) < (n : ℝ) := by rw [← hn, hsym]; exact div_pos (mul_pos two_pos hpos) hα₀
    exact_mod_cast h
  by_cases hm' : m = 1
  · rw [hm'] at hm
    simpa only [hm, Int.cast_one, one_smul] using hR.2.1 β hβ α hα
  by_cases hn' : n = 1
  · rw [hn'] at hn
    have h : β - α ∈ R := by simpa only [hn, Int.cast_one, one_smul] using hR.2.1 α hα β hβ
    simpa only [neg_sub] using hR.neg_mem h
  have hm₂ : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show (2 : ℤ) ≤ m by omega)
  have hn₂ : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show (2 : ℤ) ≤ n by omega)
  have hβle : ⟪β, β⟫ ≤ ⟪α, β⟫ := by
    have h : (2 : ℝ) ≤ 2 * ⟪α, β⟫ / ⟪β, β⟫ := by rwa [hm]
    have h := (le_div_iff₀ hβ₀).mp h
    linarith
  have hαle : ⟪α, α⟫ ≤ ⟪α, β⟫ := by
    have h : (2 : ℝ) ≤ 2 * ⟪β, α⟫ / ⟪α, α⟫ := by rwa [hn]
    have h := (le_div_iff₀ hα₀).mp h
    linarith
  have hself := real_inner_self_pos.mpr (sub_ne_zero.mpr hne)
  rw [inner_sub_left, inner_sub_right, inner_sub_right, hsym] at hself
  linarith

omit [FiniteDimensional ℝ E] in
private theorem posSet_indecomposables_obtuse (hR : IsRootSet R) (x : E)
    (hx : ∀ α ∈ R, ⟪α, x⟫ ≠ 0) {α β : indecomposables (posSet R x)} (hne : α ≠ β) : ⟪(α : E), (β : E)⟫ ≤ 0 := by
  obtain ⟨hα, hiα⟩ := Finset.mem_filter.mp α.property
  obtain ⟨hβ, hiβ⟩ := Finset.mem_filter.mp β.property
  by_contra! h
  have hr := hR.sub_mem_of_inner_pos (Finset.mem_filter.mp hα).1 (Finset.mem_filter.mp hβ).1
    (fun he => hne (Subtype.ext he)) h
  rcases lt_trichotomy ⟪(α : E), x⟫ ⟪(β : E), x⟫ with hlt | heq | hgt
  · apply hiβ
    refine ⟨β - α, Finset.mem_filter.mpr ⟨?_, ?_⟩, α, hα, sub_add_cancel _ _ |>.symm⟩
    · simpa only [neg_sub] using hR.neg_mem hr
    · rw [inner_sub_left]; exact sub_pos.mpr hlt
  · apply hx _ hr
    rw [inner_sub_left, heq, sub_self]
  · apply hiα
    refine ⟨α - β, Finset.mem_filter.mpr ⟨hr, ?_⟩, β, hβ, sub_add_cancel _ _ |>.symm⟩
    rw [inner_sub_left]; exact sub_pos.mpr hgt

omit [FiniteDimensional ℝ E] in
private theorem linearIndependent_of_obtuse_of_pos {ι : Type*} [Fintype ι] {v : ι → E}
    (f : Module.Dual ℝ E) (hf : ∀ i, 0 < f (v i))
    (ho : ∀ i j, i ≠ j → ⟪v i, v j⟫ ≤ 0) : LinearIndependent ℝ v := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  let cp (i : ι) := max (c i) 0
  let cn (i : ι) := max (-c i) 0
  have hp i : 0 ≤ cp i := le_max_right _ _
  have hn i : 0 ≤ cn i := le_max_right _ _
  have hcpn (i : ι) : cp i - cn i = c i := by
    dsimp [cp, cn]
    rcases le_total (c i) 0 with hi | hi
    · rw [max_eq_right hi, max_eq_left (neg_nonneg.mpr hi), zero_sub, neg_neg]
    · rw [max_eq_left hi, max_eq_right (neg_nonpos.mpr hi), sub_zero]
  let xp := ∑ i, cp i • v i
  let xn := ∑ i, cn i • v i
  have hxp : xp = xn := sub_eq_zero.mp (by
    dsimp [xp, xn]
    rw [← Finset.sum_sub_distrib]
    simpa only [← sub_smul, hcpn] using hc)
  have hpair : ⟪xp, xn⟫ ≤ 0 := by
    simp only [xp, xn, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    apply Finset.sum_nonpos
    intro i _
    apply Finset.sum_nonpos
    intro j _
    by_cases hij : i = j
    · subst j
      rcases le_total (c i) 0 with hi | hi
      · simp [cp, max_eq_right hi]
      · simp [cn, max_eq_right (neg_nonpos.mpr hi)]
    · exact mul_nonpos_of_nonneg_of_nonpos (hn i)
        (mul_nonpos_of_nonneg_of_nonpos (hp j) (ho j i (Ne.symm hij)))
  have hx₀ : xp = 0 := by
    rw [← hxp] at hpair
    by_contra hx
    exact (not_lt_of_ge hpair) (real_inner_self_pos.mpr hx)
  have hcp : ∀ i, cp i = 0 := by
    have hsum := congrArg f hx₀
    simp only [xp, map_sum, map_smul, smul_eq_mul, map_zero] at hsum
    intro i
    have h := (Fintype.sum_eq_zero_iff_of_nonneg (fun j => mul_nonneg (hp j) (hf j).le)).mp hsum
    have h := congrFun h i
    exact (mul_eq_zero.mp h).resolve_right (hf i).ne'
  have hcn : ∀ i, cn i = 0 := by
    have hsum := congrArg f (hxp.symm.trans hx₀)
    simp only [xn, map_sum, map_smul, smul_eq_mul, map_zero] at hsum
    intro i
    have h := (Fintype.sum_eq_zero_iff_of_nonneg (fun j => mul_nonneg (hn j) (hf j).le)).mp hsum
    have h := congrFun h i
    exact (mul_eq_zero.mp h).resolve_right (hf i).ne'
  intro i
  rw [← hcpn i, hcp i, hcn i, sub_zero]

omit [FiniteDimensional ℝ E] in
private theorem linearIndependent_posSet_indecomposables (hR : IsRootSet R) (x : E)
    (hx : ∀ α ∈ R, ⟪α, x⟫ ≠ 0) :
    LinearIndependent ℝ (fun α : indecomposables (posSet R x) => (α : E)) := by
  apply linearIndependent_of_obtuse_of_pos (innerSL ℝ x).toLinearMap
  · intro i
    rw [ContinuousLinearMap.coe_coe, innerSL_apply_apply, real_inner_comm]
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp i.property).1).2
  · intro i j hij
    exact posSet_indecomposables_obtuse hR x hx hij

/-- A finite root arrangement has a regular point in any subspace relative to that subspace. -/
theorem exists_regular_point (R : Finset E) (a : Submodule ℝ E) :
    ∃ h, IsRegular R a h := by
  classical
  let s := R.filter fun α => restrictedRoot a α ≠ 0
  let f (α : s) : Module.Dual ℝ a := (innerSL ℝ (restrictedRoot a α)).toLinearMap
  obtain ⟨x, hx⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists f (fun α =>
    ⟨restrictedRoot a α, (real_inner_self_pos.mpr (Finset.mem_filter.mp α.property).2).ne'⟩)
  refine ⟨x, x.property, fun α hα ha => ?_⟩
  rw [← inner_restrictedRoot_subtype a α x]
  exact hx ⟨α, Finset.mem_filter.mpr ⟨hα, ha⟩⟩

/-- The roots that vanish at a regular point of a subspace are the roots that vanish
identically on it. -/
theorem IsRegular.inner_eq_zero_iff {a : Submodule ℝ E} {x α : E}
    (hx : IsRegular R a x) (hα : α ∈ R) : ⟪α, x⟫ = 0 ↔ restrictedRoot a α = 0 :=
  ⟨fun h => Classical.byContradiction (fun hn => hx.2 α hα hn h),
    fun h => (restrictedRoot_eq_zero_iff_forall_inner a α).mp h x hx.1⟩

/-- A regular point of a Levi flat cuts out the same flat as any defining point. -/
theorem IsLeviSpace.eq_leviSpaceOf_of_regular {a : Submodule ℝ E} {x : E}
    (ha : IsLeviSpace R a) (hx : IsRegular R a x) : a = leviSpaceOf R x :=
  (leviSpaceOf_eq_of_isRegular ha hx).symm

omit [FiniteDimensional ℝ E] in
private theorem exists_refining_regular (hR : IsRootSet R) (x : E) :
    ∃ y : E, (∀ α ∈ R, ⟪α, y⟫ ≠ 0) ∧
      (∀ α ∈ R, ⟪α, x⟫ ≠ 0 → 0 < ⟪α, x⟫ * ⟪α, y⟫) := by
  let f (α : R) : Module.Dual ℝ E := (innerSL ℝ (α : E)).toLinearMap
  obtain ⟨g, hg⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists f (fun α =>
    ⟨α, (real_inner_self_pos.mpr (fun h => hR.1 (h ▸ α.property))).ne'⟩)
  let t : ℝ := 1 + ∑ α : R, |f α g / f α x|
  have hmul (α : R) (hα : f α x ≠ 0) : 0 < f α x * f α (t • x + g) := by
    have hle : |f α g / f α x| ≤ ∑ β : R, |f β g / f β x| :=
      Finset.single_le_sum (f := fun β : R => |f β g / f β x|)
        (fun β _ => abs_nonneg _) (Finset.mem_univ α)
    have hneg := neg_abs_le (f α g / f α x)
    have hpos : 0 < t + f α g / f α x := by
      change 0 < (1 + ∑ β : R, |f β g / f β x|) + f α g / f α x
      linarith only [hle, hneg]
    have heq : f α x * f α (t • x + g) = f α x ^ 2 * (t + f α g / f α x) := by
      simp only [map_add, map_smul, smul_eq_mul]
      field_simp
    rw [heq]
    exact mul_pos (sq_pos_of_ne_zero hα) hpos
  refine ⟨t • x + g, ?_, fun α hα => hmul ⟨α, hα⟩⟩
  intro α hα
  change f ⟨α, hα⟩ (t • x + g) ≠ 0
  by_cases h : f ⟨α, hα⟩ x = 0
  · simpa [map_add, map_smul, h] using hg ⟨α, hα⟩
  · exact (mul_ne_zero_iff.mp (hmul ⟨α, hα⟩ h).ne').2

variable {a : Submodule ℝ E} {x y : E}

omit [FiniteDimensional ℝ E] in
private theorem pair_nonneg_of_pos_refinement
    (href : ∀ α ∈ R, ⟪α, x⟫ ≠ 0 → 0 < ⟪α, x⟫ * ⟪α, y⟫)
    {α : E} (hα : α ∈ posSet R y) : 0 ≤ ⟪α, x⟫ := by
  obtain ⟨hR, hp⟩ := Finset.mem_filter.mp hα
  by_contra! h
  exact (mul_neg_of_neg_of_pos h hp).not_gt (href α hR h.ne)

omit [FiniteDimensional ℝ E] in
private theorem exists_pos_sum (hα : α ∈ posSet R y) :
    ∃ c : indecomposables (posSet R y) → ℕ, ∑ i, c i • (i : E) = α := by
  apply exists_sum_indecomposables (posSet R y) (innerSL ℝ y).toLinearMap _ hα
  intro w hw
  simpa only [ContinuousLinearMap.coe_coe, innerSL_apply_apply, real_inner_comm y w] using
    (Finset.mem_filter.mp hw).2

omit [FiniteDimensional ℝ E] in
private theorem orthogonal_span_vanishing_simples (hR : IsRootSet R) (hy : ∀ α ∈ R, ⟪α, y⟫ ≠ 0)
    (href : ∀ α ∈ R, ⟪α, x⟫ ≠ 0 → 0 < ⟪α, x⟫ * ⟪α, y⟫) :
    (Submodule.span ℝ {α : E | α ∈ indecomposables (posSet R y) ∧ ⟪α, x⟫ = 0})ᗮ =
      leviSpaceOf R x := by
  let Z : Set E := {α : E | α ∈ indecomposables (posSet R y) ∧ ⟪α, x⟫ = 0}
  have hv : ∀ h : E, h ∈ (Submodule.span ℝ Z)ᗮ ↔ ∀ α ∈ Z, ⟪α, h⟫ = 0 := by
    intro h
    rw [Submodule.mem_orthogonal]
    exact ⟨fun hh α hα => hh α (Submodule.subset_span hα), fun hh α hα => by
      change α ∈ Submodule.span ℝ Z at hα
      induction hα using Submodule.span_induction with
      | mem _ hp => exact hh _ hp
      | zero => simp
      | add _ _ _ _ hp hq => simp [inner_add_left, hp, hq]
      | smul _ _ _ hp => simp [real_inner_smul_left, hp]⟩
  have heval (h : E) (hh : ∀ α ∈ Z, ⟪α, h⟫ = 0) {α : E} (hα : α ∈ posSet R y)
      (hαx : ⟪α, x⟫ = 0) : ⟪α, h⟫ = 0 := by
    obtain ⟨c, hc⟩ := exists_pos_sum hα
    have hsum : ∑ i, (c i : ℝ) * ⟪(i : E), x⟫ = 0 := by
      rw [← hc, sum_inner] at hαx
      simpa only [← Nat.cast_smul_eq_nsmul ℝ, real_inner_smul_left] using hαx
    have hnonneg (i : indecomposables (posSet R y)) : 0 ≤ ⟪(i : E), x⟫ :=
      pair_nonneg_of_pos_refinement href (Finset.mem_filter.mp i.property).1
    have hz (i : indecomposables (posSet R y)) : (c i : ℝ) * ⟪(i : E), x⟫ = 0 := by
      have hz := (Fintype.sum_eq_zero_iff_of_nonneg (fun i => mul_nonneg (by positivity)
        (hnonneg i))).mp hsum
      exact congrFun hz i
    rw [← hc, sum_inner]
    apply Finset.sum_eq_zero
    intro i _
    rcases mul_eq_zero.mp (hz i) with hi | hi
    · have hci : c i = 0 := by exact_mod_cast hi
      simp [hci]
    · have hzero := hh (i : E) (show (i : E) ∈ Z from ⟨i.property, hi⟩)
      rw [← Nat.cast_smul_eq_nsmul ℝ, real_inner_smul_left, hzero, mul_zero]
  ext h
  rw [hv, leviSpaceOf]
  simp only [Submodule.mem_iInf, Submodule.mem_orthogonal_singleton_iff_inner_right]
  constructor
  · intro hh α hα
    obtain ⟨hαR, hαx⟩ := Finset.mem_filter.mp hα
    rcases (hy α hαR).lt_or_gt with hn | hp
    · have hneg : (-α) ∈ posSet R y := Finset.mem_filter.mpr ⟨hR.neg_mem hαR, by
        rwa [inner_neg_left, neg_pos]⟩
      have hzero := heval h hh hneg (by rw [inner_neg_left, hαx, neg_zero])
      simpa only [inner_neg_left, neg_eq_zero] using hzero
    · exact heval h hh (Finset.mem_filter.mpr ⟨hαR, hp⟩) hαx
  · intro hh α hα
    obtain ⟨hi, hαx⟩ := hα
    exact hh α (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1, hαx⟩)

section Projection

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (S : Finset V) (T : Finset W) (f : Module.Dual ℝ V) (p : V →ₗ[ℝ] W)

private abbrev surviving : Type _ := {i : indecomposables S // p (i : V) ≠ 0}

private theorem projected_sum (hf : ∀ x ∈ S, 0 < f x) {v : V} (hv : v ∈ S) :
    ∃ c : surviving S p → ℕ, ∑ i, c i • p (i : V) = p v := by
  obtain ⟨c, hc⟩ := exists_sum_indecomposables S f hf hv
  refine ⟨fun i => c i.val, ?_⟩
  have h := congrArg p hc
  simp only [map_sum, map_nsmul] at h
  rw [← h]
  calc
    ∑ i : surviving S p, c i.val • p (i : V) =
        ∑ i ∈ Finset.univ.filter (fun i : indecomposables S => p (i : V) ≠ 0),
          c i • p (i : V) := by
      symm
      exact Finset.sum_subtype _ (p := fun i : indecomposables S => p (i : V) ≠ 0)
        (fun i => by simp) _
    _ = _ := ?_
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i _ hi
  have hz : p (i : V) = 0 := by simpa using hi
  simp [hz]

private theorem indecomposables_eq_image
    (hf : ∀ x ∈ S, 0 < f x) (hmap : ∀ x ∈ S, p x = 0 ∨ p x ∈ T)
    (hlift : ∀ w ∈ T, ∃ v ∈ S, p v = w) (hT : (0 : W) ∉ T)
    (hlinear : LinearIndependent ℝ (fun i : surviving S p => p (i : V))) :
    indecomposables T = Finset.univ.image (fun i : surviving S p => p (i : V)) := by
  ext w
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hw
    obtain ⟨hwT, hwatom⟩ := Finset.mem_filter.mp hw
    have hw₀ : w ≠ 0 := by rintro rfl; exact hT hwT
    obtain ⟨v, hv, he⟩ := hlift w hwT
    let height (v : V) := (S.filter fun u => f u < f v).card
    revert hv he
    induction v using (measure height).wf.induction with
    | h v ih =>
      intro hv he
      by_cases hatom : v ∈ indecomposables S
      · exact ⟨⟨⟨v, hatom⟩, he ▸ hw₀⟩, he⟩
      · have hdec : ∃ u ∈ S, ∃ v' ∈ S, v = u + v' := by
          simpa [indecomposables, hv] using hatom
        obtain ⟨u, hu, v', hv', rfl⟩ := hdec
        have hfu : f u < f (u + v') := by rw [map_add]; exact lt_add_of_pos_right _ (hf v' hv')
        have hfv : f v' < f (u + v') := by rw [map_add]; exact lt_add_of_pos_left _ (hf u hu)
        rw [map_add] at he
        rcases hmap u hu with hu₀ | huT
        · exact ih v' (card_lt_filter_of_lt S f hv' hfv) hv' (by simpa [hu₀] using he)
        rcases hmap v' hv' with hv₀ | hvT
        · exact ih u (card_lt_filter_of_lt S f hu hfu) hu (by simpa [hv₀] using he)
        · exact (hwatom ⟨p u, huT, p v', hvT, he.symm⟩).elim
  · rintro ⟨i, rfl⟩
    have hiS : (i : V) ∈ S := (Finset.mem_filter.mp i.val.property).1
    refine Finset.mem_filter.mpr ⟨(hmap _ hiS).resolve_left i.property, ?_⟩
    rintro ⟨x, hx, y, hy, hxy⟩
    obtain ⟨vx, hvx, hx'⟩ := hlift x hx
    obtain ⟨vy, hvy, hy'⟩ := hlift y hy
    obtain ⟨c, hc⟩ := projected_sum S f p hf hvx
    obtain ⟨d, hd⟩ := projected_sum S f p hf hvy
    rw [hx'] at hc
    rw [hy'] at hd
    let e (j : surviving S p) : ℕ := if j = i then 1 else 0
    have hsum : ∑ j, e j • p (j : V) = ∑ j, (c j + d j) • p (j : V) := by
      simp only [e, ite_smul, one_nsmul, zero_nsmul, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true, add_nsmul, Finset.sum_add_distrib, hc, hd, hxy]
    have hsumR : ∑ j, (e j : ℝ) • p (j : V) = ∑ j, ((c j + d j : ℕ) : ℝ) • p (j : V) := by
      simpa only [Nat.cast_smul_eq_nsmul] using hsum
    have heq (j : surviving S p) : e j = c j + d j := by
      exact_mod_cast hlinear.eq_coords_of_eq hsumR j
    have hoff (j : surviving S p) (hji : j ≠ i) : c j = 0 ∧ d j = 0 := by
      have h := heq j
      simp [e, hji] at h
      omega
    have hi := heq i
    simp only [e, ite_eq_left rfl] at hi
    have hzero : c i = 0 ∨ d i = 0 := by omega
    rcases hzero with hci | hdi
    · apply hT (show (0 : W) ∈ T from ?_)
      have h0 (j : surviving S p) : c j = 0 := by
        by_cases hj : j = i
        · rwa [hj]
        · exact (hoff j hj).1
      rw [← hc] at hx
      simpa [h0] using hx
    · apply hT (show (0 : W) ∈ T from ?_)
      have h0 (j : surviving S p) : d j = 0 := by
        by_cases hj : j = i
        · rwa [hj]
        · exact (hoff j hj).2
      rw [← hd] at hy
      simpa [h0] using hy

end Projection

private theorem simpleRoots_eq_indecomposables (a : Submodule ℝ E) (S : Finset E) :
    simpleRoots a S = indecomposables (restrictedRoots a S) := by
  ext w
  simp only [simpleRoots, indecomposables, Finset.mem_filter]

/-- The indecomposable positive restrictions form a linearly independent family on a Levi flat. -/
theorem linearIndependent_simpleRoots (hR : IsRootSet R) (ha : IsLeviSpace R a)
    {S : Finset E} (hS : S ∈ parabolics R a) :
    LinearIndependent ℝ (fun i : simpleRoots a S => (i : a)) := by
  obtain ⟨x, hx, rfl⟩ := (Finset.mem_filter.mp hS).2
  obtain ⟨y, hy, href⟩ := exists_refining_regular hR x
  let S := posSet R y
  let T := restrictedRoots a (posSet R x)
  let p := a.orthogonalProjectionOnto.toLinearMap
  let f := (innerSL ℝ y).toLinearMap
  have hf (α : E) (hα : α ∈ S) : 0 < f α := by
    simpa only [f, ContinuousLinearMap.coe_coe, innerSL_apply_apply, real_inner_comm y α] using
      (Finset.mem_filter.mp hα).2
  have hmap (α : E) (hα : α ∈ S) : p α = 0 ∨ p α ∈ T := by
    obtain ⟨hαR, -⟩ := Finset.mem_filter.mp hα
    rcases (pair_nonneg_of_pos_refinement href hα).eq_or_lt with hzero | hpos
    · exact Or.inl ((hx.inner_eq_zero_iff hαR).mp hzero.symm)
    · exact Or.inr (Finset.mem_image.mpr ⟨α, Finset.mem_filter.mpr ⟨hαR, hpos⟩, rfl⟩)
  have hlift (v : a) (hv : v ∈ T) : ∃ α ∈ S, p α = v := by
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hαR, hpos⟩ := Finset.mem_filter.mp hα
    exact ⟨α, Finset.mem_filter.mpr ⟨hαR, pos_of_mul_pos_right (href α hαR hpos.ne') hpos.le⟩,
      rfl⟩
  have hT : (0 : a) ∉ T := by
    intro h
    obtain ⟨α, hα, hzero⟩ := Finset.mem_image.mp h
    exact (Finset.mem_filter.mp hα).2.ne' ((restrictedRoot_eq_zero_iff_forall_inner a α).mp hzero x hx.1)
  let A := indecomposables S
  let Z : Set E := {α : E | α ∈ A ∧ ⟪α, x⟫ = 0}
  have hker : LinearMap.ker p = Submodule.span ℝ Z := by
    change a.orthogonalProjectionOnto.ker = _
    rw [Submodule.ker_orthogonalProjectionOnto, ha.eq_leviSpaceOf_of_regular hx,
      ← orthogonal_span_vanishing_simples hR hy href, Submodule.orthogonal_orthogonal]
  have hambient := linearIndependent_posSet_indecomposables hR y hy
  have hi : LinearIndependent ℝ (fun i : surviving S p => p (i : E)) := by
    have hsub := hambient.comp (fun i : surviving S p => i.val) Subtype.val_injective
    apply hsub.map
    rw [hker]
    let pos : Set A := {i | p (i : E) ≠ 0}
    let zero : Set A := {i | ⟪(i : E), x⟫ = 0}
    have hd : Disjoint pos zero := by
      refine Set.disjoint_left.mpr fun i hi hz => hi ?_
      exact (hx.inner_eq_zero_iff (Finset.mem_filter.mp (Finset.mem_filter.mp i.property).1).1).mp hz
    refine (hambient.disjoint_span_image hd).mono (Submodule.span_mono ?_) (Submodule.span_mono ?_)
    · rintro _ ⟨i, rfl⟩
      exact ⟨i.val, i.property, rfl⟩
    · rintro _ ⟨h, hz⟩
      exact ⟨⟨_, h⟩, hz, rfl⟩
  rw [simpleRoots_eq_indecomposables]
  change LinearIndependent ℝ (fun i : indecomposables T => (i : a))
  exact hi.linearIndepOn_id' (by
    rw [indecomposables_eq_image S T f p hf hmap hlift hT hi]
    simp)

/-- Every positive restricted root is a sum of simple restricted roots with natural-number
multiplicities. -/
theorem exists_sum_simpleRoots {S : Finset E} (hS : S ∈ parabolics R a) {v : a}
    (hv : v ∈ restrictedRoots a S) : ∃ c : simpleRoots a S → ℕ, ∑ i, c i • (i : a) = v := by
  obtain ⟨x, hx, rfl⟩ := (Finset.mem_filter.mp hS).2
  rw [simpleRoots_eq_indecomposables]
  apply exists_sum_indecomposables _ (innerSL ℝ (⟨x, hx.1⟩ : a)).toLinearMap _ hv
  intro w hw
  obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp hw
  simpa only [ContinuousLinearMap.coe_coe, innerSL_apply_apply,
    real_inner_comm (restrictedRoot a α) (⟨x, hx.1⟩ : a), inner_restrictedRoot_subtype] using (Finset.mem_filter.mp hα).2

omit [FiniteDimensional ℝ E] in
/-- The Levi roots of a face consist of the roots vanishing on its representative point. -/
theorem mem_leviRoots_posSet_iff (hR : IsRootSet R) (w α : E) :
    α ∈ leviRoots R (posSet R w) ↔ α ∈ R ∧ ⟪α, w⟫ = 0 := by
  constructor
  · intro h
    obtain ⟨hα, hn, hneg⟩ := Finset.mem_filter.mp h
    refine ⟨hα, ?_⟩
    apply le_antisymm
    · exact le_of_not_gt fun hp => hn (Finset.mem_filter.mpr ⟨hα, hp⟩)
    · refine le_of_not_gt fun hm => hneg (Finset.mem_filter.mpr ⟨hR.neg_mem hα, ?_⟩)
      rw [inner_neg_left, neg_pos]
      exact hm
  · rintro ⟨hα, he⟩
    refine Finset.mem_filter.mpr ⟨hα, fun h => ?_, fun h => ?_⟩
    · exact (Finset.mem_filter.mp h).2.ne' he
    · have h := (Finset.mem_filter.mp h).2
      simp [inner_neg_left, he] at h

omit [FiniteDimensional ℝ E] in
/-- Membership in the face space is membership in `a` and orthogonality to the roots that
vanish at the chosen point. -/
theorem mem_faceSpace_posSet_iff (hR : IsRootSet R) {h w : E} :
    w ∈ faceSpace R a (posSet R h) ↔ w ∈ a ∧ ∀ α ∈ R, ⟪α, h⟫ = 0 → ⟪α, w⟫ = 0 := by
  simp only [faceSpace, Submodule.mem_inf, Submodule.mem_iInf,
    Submodule.mem_orthogonal_singleton_iff_inner_right, mem_leviRoots_posSet_iff hR, and_imp]

/-- A point of a chamber closure can be tested against the simple restricted roots. -/
theorem nonneg_posSet_of_nonneg_simpleRoots {P : Finset E} (hP : P ∈ parabolics R a) (w : a)
    (hw : ∀ i : simpleRoots a P, 0 ≤ ⟪(i : a), w⟫) : ∀ α ∈ P, 0 ≤ ⟪α, (w : E)⟫ := by
  intro α hα
  have hmem : restrictedRoot a α ∈ restrictedRoots a P := Finset.mem_image_of_mem _ hα
  obtain ⟨c, hc⟩ := exists_sum_simpleRoots hP hmem
  rw [← inner_restrictedRoot_subtype a α w, ← hc, sum_inner]
  simp only [← Nat.cast_smul_eq_nsmul ℝ, real_inner_smul_left]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (hw i)

/-- The face at `w` is incident to a chamber exactly when all its positive roots have
nonnegative evaluation at `w`. -/
theorem posSet_subset_iff_nonneg (hR : IsRootSet R) {P : Finset E} (hP : P ∈ parabolics R a)
    (w : a) : posSet R (w : E) ⊆ P ↔ ∀ α ∈ P, 0 ≤ ⟪α, (w : E)⟫ := by
  obtain ⟨x, hx, rfl⟩ := (Finset.mem_filter.mp hP).2
  constructor
  · intro hw α hα
    obtain ⟨hαR, hp⟩ := Finset.mem_filter.mp hα
    by_contra! hn
    have hneg : -α ∈ posSet R (w : E) := Finset.mem_filter.mpr ⟨hR.neg_mem hαR, by
      rwa [inner_neg_left, neg_pos]⟩
    have hpos := (Finset.mem_filter.mp (hw hneg)).2
    rw [inner_neg_left, neg_pos] at hpos
    exact (lt_asymm hp) hpos
  · intro hw α hα
    obtain ⟨hαR, hp⟩ := Finset.mem_filter.mp hα
    refine Finset.mem_filter.mpr ⟨hαR, ?_⟩
    have hne : restrictedRoot a α ≠ 0 := fun hz => hp.ne'
      ((restrictedRoot_eq_zero_iff_forall_inner a α).mp hz w w.property)
    rcases (hx.2 α hαR hne).lt_or_gt with hneg | hpos
    · have hnegmem : -α ∈ posSet R x := Finset.mem_filter.mpr ⟨hR.neg_mem hαR, by
        rwa [inner_neg_left, neg_pos]⟩
      have h := hw _ hnegmem
      rw [inner_neg_left, neg_nonneg] at h
      exact (hp.not_ge h).elim
    · exact hpos

/-- The simple roots for the local chamber at an incident face are exactly the simple roots
that vanish on that face. -/
theorem simpleRoots_inter_leviRoots (hR : IsRootSet R) {P : Finset E} (hP : P ∈ parabolics R a)
    (w : a) (hw : posSet R (w : E) ⊆ P) :
    simpleRoots a (P ∩ leviRoots R (posSet R (w : E))) =
      (simpleRoots a P).filter (fun v => ⟪v, w⟫ = 0) := by
  have hnonneg : ∀ v ∈ restrictedRoots a P, 0 ≤ ⟪v, w⟫ := by
    intro v hv
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp hv
    rw [inner_restrictedRoot_subtype]
    exact (posSet_subset_iff_nonneg hR hP w).mp hw α hα
  have heq : restrictedRoots a (P ∩ leviRoots R (posSet R (w : E))) =
      (restrictedRoots a P).filter (fun v => ⟪v, w⟫ = 0) := by
    ext v
    simp only [restrictedRoots, Finset.mem_filter, Finset.mem_image, Finset.mem_inter,
      mem_leviRoots_posSet_iff hR]
    constructor
    · rintro ⟨α, ⟨hα, -, hαw⟩, rfl⟩
      exact ⟨⟨α, hα, rfl⟩, by rwa [inner_restrictedRoot_subtype]⟩
    · rintro ⟨⟨α, hα, rfl⟩, hw'⟩
      refine ⟨α, ⟨hα, ?_, by rwa [← inner_restrictedRoot_subtype a α w]⟩, rfl⟩
      exact Finset.mem_powerset.mp (Finset.mem_filter.mp hP).1 hα
  ext v
  simp only [simpleRoots, heq, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hv, hz⟩, hnd⟩
    refine ⟨⟨hv, ?_⟩, hz⟩
    rintro ⟨u, hu, t, ht, he⟩
    rw [he, inner_add_left] at hz
    have hu' := hnonneg u hu
    have ht' := hnonneg t ht
    exact hnd ⟨u, ⟨hu, by linarith⟩, t, ⟨ht, by linarith⟩, he⟩
  · rintro ⟨⟨hv, hnd⟩, hz⟩
    refine ⟨⟨hv, hz⟩, ?_⟩
    rintro ⟨u, ⟨hu, -⟩, t, ⟨ht, -⟩, ht'⟩
    exact hnd ⟨u, hu, t, ht, ht'⟩

/-- Intersecting with the Levi roots gives a bijection from incident chambers to local chambers. -/
theorem inter_leviRoots_parabolic (hR : IsRootSet R) {P : Finset E} (hP : P ∈ parabolics R a)
    (w : a) (hw : posSet R (w : E) ⊆ P) :
    P ∩ leviRoots R (posSet R (w : E)) ∈ parabolics (leviRoots R (posSet R (w : E))) a ∧
      posSet R (w : E) ∪ (P ∩ leviRoots R (posSet R (w : E))) = P := by
  obtain ⟨x, hx, rfl⟩ := (Finset.mem_filter.mp hP).2
  constructor
  · refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right, x,
      ⟨hx.1, fun α hα => hx.2 α ((mem_leviRoots_posSet_iff hR _ _).mp hα).1⟩, ?_⟩
    ext α
    simp only [Finset.mem_inter, show α ∈ posSet R x ↔ α ∈ R ∧ 0 < ⟪α, x⟫ from Finset.mem_filter,
      show α ∈ posSet (leviRoots R (posSet R (w : E))) x ↔
        α ∈ leviRoots R (posSet R (w : E)) ∧ 0 < ⟪α, x⟫ from Finset.mem_filter,
      mem_leviRoots_posSet_iff hR]
    tauto
  · apply Finset.Subset.antisymm (Finset.union_subset hw Finset.inter_subset_left)
    intro α hα
    obtain ⟨hαR, -⟩ := Finset.mem_filter.mp hα
    have hnonneg := (posSet_subset_iff_nonneg hR hP w).mp hw α hα
    rcases hnonneg.eq_or_lt with hz | hp
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr
        ⟨hα, (mem_leviRoots_posSet_iff hR _ _).mpr ⟨hαR, hz.symm⟩⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hαR, hp⟩)

/-- A chamber of the roots vanishing at `w` extends uniquely by the signs at `w`. -/
theorem union_parabolic_of_local (hR : IsRootSet R) (w : a) {S : Finset E}
    (hS : S ∈ parabolics (leviRoots R (posSet R (w : E))) a) :
    posSet R (w : E) ∪ S ∈ parabolics R a ∧
      (posSet R (w : E) ∪ S) ∩ leviRoots R (posSet R (w : E)) = S := by
  obtain ⟨x, hx, rfl⟩ := (Finset.mem_filter.mp hS).2
  let f (α : R) : ℝ := ⟪(α : E), (w : E)⟫
  let g (α : R) : ℝ := ⟪(α : E), x⟫
  let t : ℝ := 1 + ∑ α : R, |g α / f α|
  let y : E := t • (w : E) + x
  have hpair (α : R) (hn : f α ≠ 0) : 0 < f α * ⟪(α : E), y⟫ := by
    have hle : |g α / f α| ≤ ∑ β : R, |g β / f β| :=
      Finset.single_le_sum (f := fun β : R => |g β / f β|) (fun β _ => abs_nonneg _) (Finset.mem_univ α)
    have hnab := neg_abs_le (g α / f α)
    have hp : 0 < t + g α / f α := by
      change 0 < (1 + ∑ β : R, |g β / f β|) + g α / f α
      linarith only [hle, hnab]
    have he : f α * ⟪(α : E), y⟫ = f α ^ 2 * (t + g α / f α) := by
      rw [show ⟪(α : E), y⟫ = t * f α + g α from by simp [y, f, g, inner_add_right, real_inner_smul_right]]
      field_simp
    rw [he]
    exact mul_pos (sq_pos_of_ne_zero hn) hp
  have hz (α : E) (hα : ⟪α, (w : E)⟫ = 0) : ⟪α, y⟫ = ⟪α, x⟫ := by
    simp [y, inner_add_right, real_inner_smul_right, hα]
  have heq : posSet R (w : E) ∪ posSet (leviRoots R (posSet R (w : E))) x = posSet R y := by
    ext α
    simp only [Finset.mem_union, posSet, Finset.mem_filter]
    have hlevi : α ∈ leviRoots R (R.filter fun β => 0 < ⟪β, (w : E)⟫) ↔
        α ∈ R ∧ ⟪α, (w : E)⟫ = 0 := mem_leviRoots_posSet_iff hR _ _
    rw [hlevi]
    by_cases hα : α ∈ R
    · by_cases hαw : ⟪α, (w : E)⟫ = 0
      · simp [hα, hαw, hz α hαw]
      · have hp := hpair ⟨α, hα⟩ hαw
        change 0 < ⟪α, (w : E)⟫ * ⟪α, y⟫ at hp
        rcases mul_pos_iff.mp hp with hp | hn
        · simp [hα, hαw, hp.1, hp.2]
        · simp [hα, hαw, hn.1.not_gt, hn.2.not_gt]
    · simp [hα]
  refine ⟨?_, ?_⟩
  · rw [heq]
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _),
      y, ⟨a.add_mem (a.smul_mem _ w.property) hx.1, ?_⟩, rfl⟩
    intro α hα ha
    by_cases hαw : ⟪α, (w : E)⟫ = 0
    · rw [hz α hαw]
      exact hx.2 α ((mem_leviRoots_posSet_iff hR _ _).mpr ⟨hα, hαw⟩) ha
    · exact (mul_ne_zero_iff.mp (hpair ⟨α, hα⟩ hαw).ne').2
  · ext α
    simp only [Finset.mem_union, Finset.mem_inter, posSet, Finset.mem_filter]
    have hlevi : α ∈ leviRoots R (R.filter fun β => 0 < ⟪β, (w : E)⟫) ↔
        α ∈ R ∧ ⟪α, (w : E)⟫ = 0 := mem_leviRoots_posSet_iff hR _ _
    rw [hlevi]
    by_cases hαw : ⟪α, (w : E)⟫ = 0
    · simp [hαw, and_assoc]; tauto
    · simp [hαw]

omit [FiniteDimensional ℝ E] in
/-- The common root kernel is tested by all the roots in the input set. -/
theorem mem_centralSpace_iff {w : E} : w ∈ centralSpace R ↔ ∀ α ∈ R, ⟪α, w⟫ = 0 := by
  simp only [centralSpace, Submodule.mem_iInf, Submodule.mem_orthogonal_singleton_iff_inner_right]

omit [FiniteDimensional ℝ E] in
private theorem inner_zero_of_mem_orthogonal_span {V : Set E} {x : E} :
    x ∈ (Submodule.span ℝ V)ᗮ ↔ ∀ v ∈ V, ⟪v, x⟫ = 0 := by
  rw [Submodule.mem_orthogonal]
  constructor
  · intro h v hv
    exact h v (Submodule.subset_span hv)
  · intro h v hv
    induction hv using Submodule.span_induction with
    | mem _ hp => exact h _ hp
    | zero => simp
    | add _ _ _ _ hp hq => simp [inner_add_left, hp, hq]
    | smul _ _ _ hp => simp [real_inner_smul_left, hp]

/-- The common zero set of the simple roots vanishing on a face is the flat of that face. -/
theorem faceSpace_eq_orthogonal_simpleRoots (hR : IsRootSet R) {P : Finset E}
    (hP : P ∈ parabolics R a) (w : a) (hw : posSet R (w : E) ⊆ P) :
    faceSpace R a (posSet R (w : E)) = a ⊓
      (Submodule.span ℝ {v : E | ∃ i : simpleRoots a P, (i : E) = v ∧ ⟪(i : a), w⟫ = 0})ᗮ := by
  obtain ⟨x, hx, heP⟩ := (Finset.mem_filter.mp hP).2
  have hsimple (i : simpleRoots a P) : ∃ α ∈ P, restrictedRoot a α = (i : a) :=
    Finset.mem_image.mp (Finset.mem_filter.mp i.property).1
  have heval (v : a) (hv : ∀ i : simpleRoots a P, ⟪(i : a), w⟫ = 0 → ⟪(i : a), v⟫ = 0)
      {α : E} (hα : α ∈ P) (hαw : ⟪α, (w : E)⟫ = 0) : ⟪α, (v : E)⟫ = 0 := by
    obtain ⟨c, hc⟩ := exists_sum_simpleRoots hP (Finset.mem_image_of_mem (restrictedRoot a) hα)
    have hsum : ∑ i, (c i : ℝ) * ⟪(i : a), w⟫ = 0 := by
      rw [← inner_restrictedRoot_subtype a α w, ← hc, sum_inner] at hαw
      simpa only [← Nat.cast_smul_eq_nsmul ℝ, real_inner_smul_left] using hαw
    have hnonneg (i : simpleRoots a P) : 0 ≤ ⟪(i : a), w⟫ := by
      obtain ⟨β, hβ, hβi⟩ := hsimple i
      rw [← hβi, inner_restrictedRoot_subtype]
      exact (posSet_subset_iff_nonneg hR hP w).mp hw β hβ
    have hz (i : simpleRoots a P) : (c i : ℝ) * ⟪(i : a), w⟫ = 0 :=
      congrFun ((Fintype.sum_eq_zero_iff_of_nonneg (fun i => mul_nonneg (by positivity)
        (hnonneg i))).mp hsum) i
    rw [← inner_restrictedRoot_subtype a α v, ← hc, sum_inner]
    apply Finset.sum_eq_zero
    intro i _
    rw [← Nat.cast_smul_eq_nsmul ℝ, real_inner_smul_left]
    exact (mul_eq_zero.mp (hz i)).elim (fun e => by rw [e, zero_mul])
      (fun e => by rw [hv i e, mul_zero])
  ext v
  rw [mem_faceSpace_posSet_iff hR, Submodule.mem_inf, inner_zero_of_mem_orthogonal_span]
  constructor
  · rintro ⟨hva, hv⟩
    refine ⟨hva, ?_⟩
    rintro _ ⟨i, rfl, hi⟩
    obtain ⟨α, hαP, hαi⟩ := hsimple i
    have hαR : α ∈ R := Finset.mem_powerset.mp (Finset.mem_filter.mp hP).1 hαP
    change ⟪(i : a), (⟨v, hva⟩ : a)⟫ = 0
    rw [← hαi, inner_restrictedRoot_subtype]
    apply hv α hαR
    rwa [← inner_restrictedRoot_subtype a α w, hαi]
  · rintro ⟨hva, hv⟩
    refine ⟨hva, fun α hα hαw => ?_⟩
    let v' : a := ⟨v, hva⟩
    have hvs (i : simpleRoots a P) (hi : ⟪(i : a), w⟫ = 0) : ⟪(i : a), v'⟫ = 0 :=
      hv _ ⟨i, rfl, hi⟩
    by_cases hz : restrictedRoot a α = 0
    · exact (restrictedRoot_eq_zero_iff_forall_inner a α).mp hz v hva
    rcases (hx.2 α hα hz).lt_or_gt with hn | hp
    · have hneg : -α ∈ P := by
        rw [heP]
        exact Finset.mem_filter.mpr ⟨hR.neg_mem hα, by rwa [inner_neg_left, neg_pos]⟩
      simpa only [inner_neg_left, neg_eq_zero] using heval v' hvs hneg (by simp [hαw])
    · exact heval v' hvs (heP ▸ Finset.mem_filter.mpr ⟨hα, hp⟩) hαw

omit [FiniteDimensional ℝ E] in
/-- Every Levi flat contains the common root kernel. -/
theorem centralSpace_le_of_isLeviSpace (ha : IsLeviSpace R a) : centralSpace R ≤ a := by
  obtain ⟨w, rfl⟩ := ha
  intro x hx
  rw [mem_centralSpace_iff] at hx
  simp only [leviSpaceOf, Submodule.mem_iInf, Submodule.mem_orthogonal_singleton_iff_inner_right]
  exact fun α hα => hx α (Finset.mem_filter.mp hα).1

omit [FiniteDimensional ℝ E] in
/-- The face space of a point in a Levi flat is the root flat of that point. -/
theorem faceSpace_posSet_eq_leviSpaceOf (hR : IsRootSet R) (ha : IsLeviSpace R a) (w : a) :
    faceSpace R a (posSet R (w : E)) = leviSpaceOf R (w : E) := by
  have he : faceSpace R a (posSet R (w : E)) = a ⊓ leviSpaceOf R (w : E) := by
    ext x
    simp only [mem_faceSpace_posSet_iff hR, Submodule.mem_inf, leviSpaceOf, Submodule.mem_iInf,
      Submodule.mem_orthogonal_singleton_iff_inner_right, Finset.mem_filter, and_imp]
  rw [he, inf_eq_right.mpr (leviSpaceOf_le_of_mem ha w.property)]

omit [FiniteDimensional ℝ E] in
/-- The Levi spaces above a fixed Levi flat are exactly the root flats contained in it. -/
theorem mem_leviSpaces_iff (hR : IsRootSet R) (ha : IsLeviSpace R a) (L : Submodule ℝ E) :
    L ∈ leviSpaces R a ↔ L ≤ a ∧ IsLeviSpace R L := by
  constructor
  · intro hL
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hL
    obtain ⟨w, hwa, rfl⟩ := (Finset.mem_filter.mp hQ).2
    exact ⟨inf_le_left, ⟨w, faceSpace_posSet_eq_leviSpaceOf hR ha ⟨w, hwa⟩⟩⟩
  · rintro ⟨hL, ⟨w, rfl⟩⟩
    have hw : w ∈ leviSpaceOf R w := by
      simp only [leviSpaceOf, Submodule.mem_iInf, Submodule.mem_orthogonal_singleton_iff_inner_right]
      exact fun α hα => (Finset.mem_filter.mp hα).2
    refine Finset.mem_image.mpr ⟨posSet R w, ?_, faceSpace_posSet_eq_leviSpaceOf hR ha ⟨w, hL hw⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _), w, hL hw, rfl⟩

/-- The simple restricted roots span the orthogonal complement of the common root kernel in `a`. -/
theorem span_simpleRoots_eq (hR : IsRootSet R) (ha : IsLeviSpace R a) {P : Finset E}
    (hP : P ∈ parabolics R a) :
    Submodule.span ℝ (Set.range fun i : simpleRoots a P => (i : E)) = a ⊓ (centralSpace R)ᗮ := by
  let U := Submodule.span ℝ (Set.range fun i : simpleRoots a P => (i : E))
  have hz : a ⊓ Uᗮ = centralSpace R := by
    have h : faceSpace R a (posSet R (0 : E)) = a ⊓ Uᗮ := by
      convert faceSpace_eq_orthogonal_simpleRoots hR hP (0 : a) (by simp [posSet]) using 4
      ext v
      simp only [inner_zero_right, and_true, Set.mem_range, Set.mem_ofPred_eq]
    rw [← h]
    change faceSpace R a (posSet R ((0 : a) : E)) = centralSpace R
    rw [faceSpace_posSet_eq_leviSpaceOf hR ha]
    simp [leviSpaceOf, centralSpace]
  have hUa : U ≤ a := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (i : a).property)
  have hUz : U ≤ (centralSpace R)ᗮ := by
    rw [← hz]
    exact (Submodule.le_orthogonal_orthogonal U).trans (Submodule.orthogonal_le inf_le_right)
  refine le_antisymm (le_inf hUa hUz) ?_
  intro v hv
  have hvU : U.starProjection v ∈ U := U.starProjection_apply_mem v
  have hsub : v - U.starProjection v ∈ (centralSpace R) ⊓ (centralSpace R)ᗮ := by
    refine ⟨?_, (centralSpace R)ᗮ.sub_mem hv.2 (hUz hvU)⟩
    rw [← hz]
    exact ⟨a.sub_mem hv.1 (hUa hvU), U.sub_starProjection_mem_orthogonal v⟩
  rw [(centralSpace R).inf_orthogonal_eq_bot, Submodule.mem_bot, sub_eq_zero] at hsub
  rw [hsub]
  exact hvU

end Langlands.GMFamily
