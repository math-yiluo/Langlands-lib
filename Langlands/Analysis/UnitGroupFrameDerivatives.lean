import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Ring.Units

/-! # Bounds for coordinate derivatives from the unit-group frame -/

noncomputable section
set_option autoImplicit false

open scoped Classical ContDiff
open Set Filter Topology

namespace Langlands.Analysis.UnitGroupFrame

variable {A ι : Type*} [NormedRing A] [NormedAlgebra ℝ A]
  [FiniteDimensional ℝ A] [CompleteSpace A] [Fintype ι]

private def coefficient (basis : Module.Basis ι ℝ A) (i : ι) (x : A) : A →L[ℝ] ℝ :=
  (basis.coord i).toContinuousLinearMap.comp (ContinuousLinearMap.mul ℝ A (Ring.inverse x))

omit [Fintype ι] in
private theorem contDiffOn_coefficient (basis : Module.Basis ι ℝ A) (i : ι) :
    ContDiffOn ℝ ∞ (coefficient basis i) (range (Units.val : Aˣ → A)) := by
  let L := ContinuousLinearMap.mul ℝ A
  have hL : ContDiffOn ℝ ∞ (fun x => L (Ring.inverse x)) (range (Units.val : Aˣ → A)) := by
    rintro _ ⟨g, rfl⟩
    exact (L.contDiff.contDiffAt.comp _ (contDiffAt_ringInverse ℝ g)).contDiffWithinAt
  exact contDiffOn_const.clm_comp hL

private theorem exists_coefficient_bound (basis : Module.Basis ι ℝ A)
    (t : Set A) (ht : IsCompact t) (htu : t ⊆ range (Units.val : Aˣ → A)) (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i : ι, ∀ j ≤ n, ∀ x ∈ t,
      ‖iteratedFDeriv ℝ j (coefficient basis i) x‖ ≤ B := by
  let U := range (Units.val : Aˣ → A)
  have hU : IsOpen U := Units.isOpenEmbedding_val.isOpen_range
  have hcont (i : ι) (j : ℕ) : ContinuousOn (iteratedFDeriv ℝ j (coefficient basis i)) U :=
    ((contDiffOn_coefficient basis i).continuousOn_iteratedFDerivWithin
      (show (j : ℕ∞ω) ≤ ∞ by simp) hU.uniqueDiffOn).congr
      (fun _ hx => (iteratedFDerivWithin_of_isOpen j hU hx).symm)
  have hb (i : ι) (j : ℕ) : ∃ b : ℝ, 0 ≤ b ∧
      ∀ x ∈ t, ‖iteratedFDeriv ℝ j (coefficient basis i) x‖ ≤ b := by
    obtain ⟨b, hb⟩ := ht.exists_bound_of_continuousOn ((hcont i j).mono htu)
    exact ⟨max 0 b, le_max_left _ _, fun x hx => (hb x hx).trans (le_max_right _ _)⟩
  choose b hb0 hb using hb
  refine ⟨∑ i, ∑ j ∈ Finset.range (n + 1), b i j,
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hb0 i j)), ?_⟩
  intro i j hj x hx
  exact (hb i j x hx).trans <|
    (Finset.single_le_sum (fun k _ => hb0 i k) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => hb0 k l)) (Finset.mem_univ i))

variable {M : Type*} [Monoid M]

omit [CompleteSpace A] in
private theorem fderiv_eq_frame_sum (basis : Module.Basis ι ℝ A) (gen : ι → M)
    (f : M → A → ℂ)
    (hgen : ∀ m i, ∀ x ∈ range (Units.val : Aˣ → A),
      fderiv ℝ (f m) x (x * basis i) = f (gen i * m) x)
    (m : M) (x : A) (hx : x ∈ range (Units.val : Aˣ → A)) :
    fderiv ℝ (f m) x =
      ∑ i, (coefficient basis i x).smulRight (f (gen i * m) x) := by
  let L := ContinuousLinearMap.mul ℝ A x
  let T := (fderiv ℝ (f m) x).comp L
  ext z
  have hxz : x * (Ring.inverse x * z) = z := by
    obtain ⟨g, rfl⟩ := hx
    rw [Ring.inverse_unit, Units.mul_inv_cancel_left]
  calc
    fderiv ℝ (f m) x z = T (Ring.inverse x * z) :=
      congrArg (fderiv ℝ (f m) x) hxz.symm
    _ = T (∑ i, basis.repr (Ring.inverse x * z) i • basis i) :=
      congrArg T (basis.sum_repr _).symm
    _ = (∑ i, (coefficient basis i x).smulRight (f (gen i * m) x)) z := by
      rw [map_sum, sum_apply]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul]
      change basis.repr (Ring.inverse x * z) i • fderiv ℝ (f m) x (x * basis i) =
        basis.repr (Ring.inverse x * z) i • f (gen i * m) x
      rw [hgen m i x hx]

/-- On a compact subset of the unit chart, finitely many words in a
frame give a uniform bound for all coordinate derivatives up to order `N`.
The family records the exact differential law by left multiplication in
the indexing monoid. -/
theorem exists_iteratedFDeriv_le_sum_frame (basis : Module.Basis ι ℝ A) (gen : ι → M)
    (t : Set A) (ht : IsCompact t) (htu : t ⊆ range (Units.val : Aˣ → A)) (N : ℕ) :
    ∃ (D : Finset M) (C : ℝ), 0 ≤ C ∧
      ∀ (f : M → A → ℂ), (∀ m, ContDiffOn ℝ ∞ (f m) (range (Units.val : Aˣ → A))) →
        (∀ m i, ∀ x ∈ range (Units.val : Aˣ → A),
          fderiv ℝ (f m) x (x * basis i) = f (gen i * m) x) →
        ∀ m, ∀ x ∈ t, ∀ j ≤ N,
          ‖iteratedFDeriv ℝ j (f m) x‖ ≤ C * ∑ d ∈ D, ‖f (d * m) x‖ := by
  let U := range (Units.val : Aˣ → A)
  have hU : IsOpen U := Units.isOpenEmbedding_val.isOpen_range
  suffices h : ∃ (D : Finset M) (C : ℝ), 0 ≤ C ∧
      ∀ (f : M → A → ℂ), (∀ m, ContDiffOn ℝ ∞ (f m) U) →
        (∀ m i, ∀ x ∈ U, fderiv ℝ (f m) x (x * basis i) = f (gen i * m) x) →
        ∀ m, ∀ x ∈ t, ∀ R : ℝ, 0 ≤ R →
          (∀ d ∈ D, ‖f (d * m) x‖ ≤ R) →
          ∀ j ≤ N, ‖iteratedFDeriv ℝ j (f m) x‖ ≤ C * R by
    obtain ⟨D, C, hC, h⟩ := h
    refine ⟨D, C, hC, fun f hf hd m x hx => h f hf hd m x hx _ ?_ ?_⟩
    · exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    · exact fun d hd => Finset.single_le_sum (f := fun i => ‖f (i * m) x‖)
        (fun _ _ => norm_nonneg _) hd
  induction N with
  | zero =>
    refine ⟨{1}, 1, zero_le_one, ?_⟩
    intro f _ _ m x _ R _ hR j hj
    have hj' : j = 0 := Nat.le_zero.mp hj
    subst j
    have h := hR 1 (Finset.mem_singleton_self 1)
    simpa only [norm_iteratedFDeriv_zero, one_mul] using h
  | succ k ih =>
    obtain ⟨D, C, hC, hD⟩ := ih
    obtain ⟨B, hB, hbound⟩ := exists_coefficient_bound basis t ht htu k
    let : SeminormedAddCommGroup (A →L[ℝ] ℝ) := inferInstance
    let : NormedSpace ℝ (A →L[ℝ] ℝ) := inferInstance
    let : SeminormedAddCommGroup (A →L[ℝ] ℂ) := inferInstance
    let : NormedSpace ℝ (A →L[ℝ] ℂ) := inferInstance
    let : SeminormedAddCommGroup (ℂ →L[ℝ] A →L[ℝ] ℂ) := inferInstance
    let : NormedSpace ℝ (ℂ →L[ℝ] A →L[ℝ] ℂ) := inferInstance
    let D' := D ∪ Finset.univ.biUnion (fun i : ι => D.image (fun d => d * gen i))
    let L : ℝ := ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ)
    have hL : 0 ≤ L := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    let P : (A →L[ℝ] ℝ) →L[ℝ] ℂ →L[ℝ] A →L[ℝ] ℂ := ContinuousLinearMap.smulRightL ℝ A ℂ
    let C' := (Fintype.card ι : ℝ) * ‖P‖ * L * B * C
    refine ⟨D', max C C', hC.trans (le_max_left _ _), ?_⟩
    intro f hf hgen m x hx R hR hmax j hj
    have hxU : x ∈ U := htu hx
    by_cases hjk : j ≤ k
    · exact (hD f hf hgen m x hx R hR (fun d hd => hmax d (Finset.mem_union_left _ hd)) j hjk).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hR)
    have hj' : j = k + 1 := by omega
    subst j
    let p (i : ι) (y : A) := P (coefficient basis i y) (f (gen i * m) y)
    have hp (i : ι) : ContDiffOn ℝ ∞ (p i) U :=
      (P.contDiff.comp_contDiffOn (contDiffOn_coefficient basis i)).clm_apply (hf (gen i * m))
    have hlocal : fderiv ℝ (f m) =ᶠ[𝓝 x] (fun y => ∑ i, p i y) := by
      filter_upwards [hU.mem_nhds hxU] with y hy
      exact fderiv_eq_frame_sum basis gen f hgen m y hy
    have hd (i : ι) (a : ℕ) (ha : a ≤ k) :
        ‖iteratedFDeriv ℝ a (f (gen i * m)) x‖ ≤ C * R := by
      apply hD f hf hgen (gen i * m) x hx R hR _ a ha
      intro d hd
      have hd' : d * gen i ∈ D' := Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ _, Finset.mem_image_of_mem (fun z => z * gen i) hd⟩)
      simpa only [mul_assoc] using hmax (d * gen i) hd'
    have hpbound (i : ι) : ‖iteratedFDeriv ℝ k (p i) x‖ ≤ ‖P‖ * (L * (B * (C * R))) := by
      have hb := P.norm_iteratedFDerivWithin_le_of_bilinear
        (contDiffOn_coefficient basis i) (hf (gen i * m)) hU.uniqueDiffOn hxU
        (show (k : ℕ∞ω) ≤ ∞ by simp)
      rw [iteratedFDerivWithin_of_isOpen k hU hxU] at hb
      change ‖iteratedFDeriv ℝ k (p i) x‖ ≤ _ at hb
      refine hb.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg P))
      change _ ≤ (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ)) * (B * (C * R))
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro a ha
      rw [iteratedFDerivWithin_of_isOpen a hU hxU,
        iteratedFDerivWithin_of_isOpen (k - a) hU hxU, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (hbound i a (Nat.le_of_lt_succ (Finset.mem_range.mp ha)) x hx)
          (hd i (k - a) (Nat.sub_le _ _)) (norm_nonneg _) hB) (Nat.cast_nonneg _)
    rw [← norm_iteratedFDeriv_fderiv, (hlocal.iteratedFDeriv ℝ k).eq_of_nhds,
      iteratedFDeriv_fun_sum_apply (fun i _ =>
        ((hp i).contDiffAt (hU.mem_nhds hxU)).of_le (by simp))]
    calc
      ‖∑ i, iteratedFDeriv ℝ k (p i) x‖ ≤ ∑ i, ‖iteratedFDeriv ℝ k (p i) x‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _i : ι, ‖P‖ * (L * (B * (C * R))) := Finset.sum_le_sum (fun i _ => hpbound i)
      _ = C' * R := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, C']; ring
      _ ≤ max C C' * R := mul_le_mul_of_nonneg_right (le_max_right _ _) hR

end Langlands.Analysis.UnitGroupFrame
