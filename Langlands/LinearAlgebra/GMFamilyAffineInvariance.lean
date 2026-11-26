import Langlands.LinearAlgebra.GMFamilyAffineWall
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Topology.LocallyConstant.Basic

/-! # Independence of the generic affine intercepts -/

noncomputable section

open Classical Finset Filter
open scoped Topology

namespace Langlands.GMFamily.AffineBases

private theorem exists_avoiding_preserving_signs {ι U : Type*} [Fintype ι] [AddCommGroup U] [Module ℝ U]
    (f : ι → Module.Dual ℝ U) (hf : ∀ i, f i ≠ 0) (x : U) :
    ∃ y, (∀ i, f i y ≠ 0) ∧ ∀ i, f i x ≠ 0 → 0 < f i x * f i y := by
  obtain ⟨g, hg⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists f (fun i => by
    by_contra! h
    exact hf i (LinearMap.ext h))
  let c : ℝ := 1 + ∑ i, |f i g / f i x|
  have hsign (i : ι) (hi : f i x ≠ 0) : 0 < f i x * f i (c • x + g) := by
    have hle : |f i g / f i x| ≤ ∑ j, |f j g / f j x| :=
      Finset.single_le_sum (f := fun j => |f j g / f j x|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    have hn := neg_abs_le (f i g / f i x)
    have hp : 0 < c + f i g / f i x := by change 0 < (1 + ∑ j, |f j g / f j x|) + f i g / f i x; linarith
    have he : f i x * f i (c • x + g) = f i x ^ 2 * (c + f i g / f i x) := by
      simp only [map_add, map_smul, smul_eq_mul]
      field_simp
    rw [he]
    exact mul_pos (sq_pos_of_ne_zero hi) hp
  refine ⟨c • x + g, fun i => ?_, hsign⟩
  by_cases h : f i x = 0
  · simpa [h] using hg i
  · exact (mul_ne_zero_iff.mp (hsign i h).ne').2

variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype ι] (v : ι → V)

omit [FiniteDimensional ℝ V] in
/-- Every intercept vector can be made regular while preserving its already strict slacks.
An additional finite family of nonzero forms can be avoided at the same time. -/
theorem exists_regular_preserving {κ : Type*} [Fintype κ]
    (f : κ → Module.Dual ℝ (ι → ℝ)) (hf : ∀ k, f k ≠ 0) (x : ι → ℝ) :
    ∃ y, Regular v y ∧ (∀ k, f k y ≠ 0) ∧ (∀ k, f k x ≠ 0 → 0 < f k x * f k y) ∧
      ∀ B : BasisIndex v, ∀ j ∉ B.val, slack v B j x ≠ 0 → 0 < slack v B j x * slack v B j y := by
  let I := Σ B : BasisIndex v, {j : ι // j ∉ B.val}
  let F : Sum I κ → Module.Dual ℝ (ι → ℝ) := Sum.elim (fun a => slack v a.1 a.2) f
  have hF (s : Sum I κ) : F s ≠ 0 := by
    rcases s with s | k
    · exact slack_ne_zero_of_notMem v s.1 s.2.property
    · exact hf k
  obtain ⟨y, hy, hs⟩ := exists_avoiding_preserving_signs F hF x
  exact ⟨y, fun B j hj => hy (.inl ⟨B, ⟨j, hj⟩⟩), fun k => hy (.inr k),
    fun k => hs (.inr k), fun B j hj => hs (.inl ⟨B, ⟨j, hj⟩⟩)⟩

private def crossingForm (x : ι → ℝ) (f g : Module.Dual ℝ (ι → ℝ)) : Module.Dual ℝ (ι → ℝ) :=
  f x • g - g x • f

private def segment (x y : ι → ℝ) (t : ℝ) : ι → ℝ := (1 - t) • x + t • y

private theorem exists_segment_simpleWall {x y : ι → ℝ} (hx : Regular v x) (_hy : Regular v y) :
    ∃ z, Regular v z ∧ PreservesStrict v y z x ∧ ∀ t : ℝ, SimpleWall v (segment x z t) := by
  let I := Σ B : BasisIndex v, {j : ι // j ∉ B.val}
  let f (i : I) := slack v i.1 i.2
  let D := {ij : I × I // crossingForm x (f ij.1) (f ij.2) ≠ 0}
  let F (d : D) := crossingForm x (f d.val.1) (f d.val.2)
  obtain ⟨z, hz, hnon, -, hs⟩ := exists_regular_preserving v F (fun d => d.property) y
  refine ⟨z, hz, ?_, ?_⟩
  · intro B j hj hn
    have h := hs B j hj hn
    have he : 0 < slack v B j z ↔ 0 < slack v B j y := by
      rcases mul_pos_iff.mp h with hpos | hneg
      · exact iff_of_true hpos.2 hpos.1
      · exact iff_of_false hneg.2.not_gt hneg.1.not_gt
    simpa only [PositiveSlack, hz B j hj, false_and, or_false] using he
  · intro t B C j k hj hk hB hC
    let d := crossingForm x (slack v B j) (slack v C k)
    have hnx := hx C k hk
    have ht : t ≠ 0 := by
      intro h
      exact hnx (by simpa [segment, h] using hC)
    have hd : d = 0 := by
      by_contra hn
      have hdz := hnon ⟨(⟨B, ⟨j, hj⟩⟩, ⟨C, ⟨k, hk⟩⟩), hn⟩
      apply hdz
      change d z = 0
      have h : t * d z = 0 := by
        simp only [segment, map_add, map_smul, smul_eq_mul] at hB hC
        simp only [d, crossingForm, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
        linear_combination slack v B j x * hC - slack v C k x * hB
      exact (mul_eq_zero.mp h).resolve_left ht
    refine ⟨slack v B j x / slack v C k x, LinearMap.ext fun b => ?_⟩
    have he := congrArg (fun l : Module.Dual ℝ (ι → ℝ) => l b) hd
    change slack v B j x * slack v C k b - slack v C k x * slack v B j b = 0 at he
    simp only [LinearMap.smul_apply, smul_eq_mul]
    field_simp
    linarith

omit [FiniteDimensional ℝ V] [Fintype ι] in
private theorem preservesStrict_self (x g : ι → ℝ) : PreservesStrict v x x g := by
  intro B j _ h
  simp only [PositiveSlack, h, false_and, or_false]

omit [FiniteDimensional ℝ V] in
private theorem eventually_preservesStrict (x y g : ι → ℝ) (t : ℝ) :
    ∀ᶠ s in 𝓝 t, PreservesStrict v (segment x y t) (segment x y s) g := by
  simp only [PreservesStrict]
  rw [Filter.eventually_all]
  intro B
  rw [Filter.eventually_all]
  intro j
  by_cases hj : j ∈ B.val
  · exact Eventually.of_forall fun _ hn => (hn hj).elim
  let h (s : ℝ) := slack v B j (segment x y s)
  have hh : Continuous h := (slack v B j).continuous_of_finiteDimensional.comp (by
    unfold segment
    fun_prop)
  rcases lt_trichotomy (h t) 0 with hs | hzero | hs
  · have hn : ∀ᶠ s in 𝓝 t, h s < 0 := hh.continuousAt.eventually_lt continuousAt_const hs
    filter_upwards [hn] with s hn _ _
    change (0 < h s ∨ h s = 0 ∧ _) ↔ 0 < h t
    simp only [hn.not_gt, hn.ne, hs.not_gt, false_and, or_self]
  · exact Eventually.of_forall fun _ _ hn => (hn hzero).elim
  · have hn : ∀ᶠ s in 𝓝 t, 0 < h s := continuousAt_const.eventually_lt hh.continuousAt hs
    filter_upwards [hn] with s hn _ _
    change (0 < h s ∨ h s = 0 ∧ _) ↔ 0 < h t
    simp only [hn, hs, true_or]

/-- The sum with its common denominator cleared is independent of generic intercepts. -/
theorem sum_weight_eq (ℓ : V →ₗ[ℝ] ℂ) {x y : ι → ℝ} (hx : Regular v x) (hy : Regular v y) :
    (∑ B : BasisIndex v, if Feasible v B x then weight v ℓ B else 0) =
      ∑ B : BasisIndex v, if Feasible v B y then weight v ℓ B else 0 := by
  obtain ⟨z, hz, hzy, hwall⟩ := exists_segment_simpleWall v hx hy
  let F (t : ℝ) := extendedSum v ℓ (segment x z t) x
  have hF : IsLocallyConstant F := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro t
    filter_upwards [eventually_preservesStrict v x z x t] with s hs
    exact extendedSum_eq_of_preservesStrict v ℓ (hwall t) hx hs (preservesStrict_self v _ _)
  have hstep : extendedSum v ℓ x x = extendedSum v ℓ z x := by
    have h := hF.apply_eq_of_preconnectedSpace 0 1
    simpa only [F, segment, sub_zero, sub_self, zero_smul, one_smul, add_zero, zero_add] using h
  have hywall : SimpleWall v y := fun B _ j _ hj _ h _ => (hy B j hj h).elim
  have hzy := extendedSum_eq_of_preservesStrict v ℓ hywall hx hzy (preservesStrict_self v y x)
  have he (b : ι → ℝ) (hb : Regular v b) : extendedSum v ℓ b x =
      ∑ B : BasisIndex v, if Feasible v B b then weight v ℓ B else 0 := by
    unfold extendedSum Feasible
    apply sum_congr rfl
    intro B _
    have h : (∀ j, j ∉ B.val → PositiveSlack v b x B j) ↔ ∀ j, j ∉ B.val → 0 < slack v B j b := by
      apply forall_congr'
      intro j
      apply imp_congr_right
      intro hj
      simp only [PositiveSlack, hb B j hj, false_and, or_false]
    by_cases hp : ∀ j, j ∉ B.val → 0 < slack v B j b
    · rw [ite_eq_left (h.mpr hp), ite_eq_left hp]
    · rw [ite_eq_right (fun hp' => hp (h.mp hp')), ite_eq_right hp]
  exact (he x hx).symm.trans (hstep.trans (hzy.trans (he y hy)))

/-- The coefficient of a basis before clearing the common denominator. -/
def normalizedWeight (ℓ : V →ₗ[ℝ] ℂ) (B : BasisIndex v) : ℂ :=
  (gramVolume (fun i : B.val => v i) : ℂ) / ∏ i : B.val, ℓ (v i)

/-- The sum of normalized coefficients over the feasible bases is independent of the generic
intercepts of all the inequalities. -/
theorem sum_normalizedWeight_eq (ℓ : V →ₗ[ℝ] ℂ) (hℓ : ∀ i, ℓ (v i) ≠ 0)
    {x y : ι → ℝ} (hx : Regular v x) (hy : Regular v y) :
    (∑ B : BasisIndex v, if Feasible v B x then normalizedWeight v ℓ B else 0) =
      ∑ B : BasisIndex v, if Feasible v B y then normalizedWeight v ℓ B else 0 := by
  have hmul (b : ι → ℝ) :
      (∑ B : BasisIndex v, if Feasible v B b then normalizedWeight v ℓ B else 0) *
        (∏ i, ℓ (v i)) = ∑ B : BasisIndex v, if Feasible v B b then weight v ℓ B else 0 := by
    rw [Finset.sum_mul]
    apply sum_congr rfl
    intro B _
    by_cases hB : Feasible v B b
    · rw [ite_eq_left hB, ite_eq_left hB, normalizedWeight, weight,
        ← prod_sdiff (subset_univ B.val) (f := fun i => ℓ (v i)),
        Finset.univ_eq_attach, Finset.prod_attach B.val (fun i : ι => ℓ (v i))]
      field_simp [Finset.prod_ne_zero_iff.mpr fun i _ => hℓ i]
    · simp [hB]
  apply mul_right_cancel₀ (Finset.prod_ne_zero_iff.mpr fun i _ => hℓ i)
  rw [hmul x, hmul y]
  exact sum_weight_eq v ℓ hx hy

end Langlands.GMFamily.AffineBases
