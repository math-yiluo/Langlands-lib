import Langlands.LinearAlgebra.AffineVertexWeights
import Langlands.LinearAlgebra.FiniteHyperplaneChamberGallery

/-! # Wall cancellation for weighted affine vertices -/

noncomputable section

open Classical
open Langlands.GMFamily
open Langlands.LinearAlgebra.FiniteHyperplaneSegment

namespace Langlands.LinearAlgebra.AffineVertexWeights

variable {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {v : ι → V}

/-- At the specified offset, the enlarged basis support is tight and all other slacks are
    strictly positive. -/
def changesAt (A : WallIndex v) (w : ι → ℝ) : Prop :=
  wallForm v A w = 0 ∧ ∀ i ∉ wallSupport A, 0 < A.1.slack i w

private def wallSign (t : ℝ) : ℂ := if 0 < t then 1 else -1

private def wallContribution (param : V →ₗ[ℝ] ℂ) (h w : ι → ℝ) (A : WallIndex v) : ℂ :=
  if changesAt A w then wallSign (wallForm v A h) * weight v param A.1 else 0

private theorem pos_iff_of_mul_pos {x y : ℝ} (h : 0 < x * y) : 0 < x ↔ 0 < y := by
  rcases mul_pos_iff.mp h with hp | hn
  · exact iff_of_true hp.1 hp.2
  · exact iff_of_false (not_lt_of_gt hn.1) (not_lt_of_gt hn.2)

private theorem pos_iff_not_of_mul_neg {x y : ℝ} (h : x * y < 0) : 0 < y ↔ ¬ 0 < x := by
  rcases mul_neg_iff.mp h with hp | hn
  · exact iff_of_false (not_lt_of_gt hp.2) (not_not.mpr hp.1)
  · exact iff_of_true hn.2 (not_lt_of_gt hn.1)

omit [Fintype ι] in
private theorem eq_external_of_proportional (J : BasisIndex v) {i j : ι}
    (hj : j ∉ J.val) {c : ℝ} (h : J.slack j = c • J.slack i) : i = j := by
  by_contra hij
  have he := congrArg (fun l : Module.Dual ℝ (ι → ℝ) => l (Pi.single j 1)) h
  simp only [BasisIndex.slack_single_of_notMem _ _ _ hj, ite_true, LinearMap.smul_apply,
    hij, ite_false, smul_eq_mul, mul_zero, one_ne_zero] at he

private theorem contribution_eq_sum_wall (param : V →ₗ[ℝ] ℂ) (J : BasisIndex v)
    {h h' w : ι → ℝ}
    (hflip : ∀ A : WallIndex v, wallForm v A w = 0 → wallForm v A h * wallForm v A h' < 0)
    (hfixed : ∀ A : WallIndex v, wallForm v A w ≠ 0 →
      0 < wallForm v A h * wallForm v A w ∧ 0 < wallForm v A h' * wallForm v A w)
    (hprop : ∀ A B : WallIndex v, wallForm v A w = 0 → wallForm v B w = 0 →
      ∃ c : ℝ, c ≠ 0 ∧ wallForm v B = c • wallForm v A) :
    ((if ∀ j ∉ J.val, 0 < J.slack j h then weight v param J else 0) -
      (if ∀ j ∉ J.val, 0 < J.slack j h' then weight v param J else 0)) =
      ∑ i : {j : ι // j ∉ J.val}, wallContribution param h w ⟨J, i⟩ := by
  let I := {j : ι // j ∉ J.val}
  have hsame (j : I) (hj : J.slack j w ≠ 0) :
      (0 < J.slack j h ↔ 0 < J.slack j w) ∧ (0 < J.slack j h' ↔ 0 < J.slack j w) :=
    ⟨pos_iff_of_mul_pos (hfixed ⟨J, j⟩ hj).1, pos_iff_of_mul_pos (hfixed ⟨J, j⟩ hj).2⟩
  by_cases hex : ∃ i : I, J.slack i w = 0
  · obtain ⟨i, hi⟩ := hex
    have huniq (j : I) (hj : j ≠ i) : J.slack j w ≠ 0 := by
      intro hjw
      obtain ⟨c, _, hc⟩ := hprop ⟨J, i⟩ ⟨J, j⟩ hi hjw
      exact hj (Subtype.ext (eq_external_of_proportional J j.prop hc).symm)
    rw [Finset.sum_eq_single i]
    · let A : WallIndex v := ⟨J, i⟩
      have hA (k : ι) : k ∉ wallSupport A ↔ k ∉ J.val ∧ k ≠ (i : ι) := by
        simp [A, wallSupport, not_or, and_comm]
      have hrest {x : ι → ℝ} (hs : ∀ j : I, j ≠ i → (0 < J.slack j x ↔ 0 < J.slack j w)) :
          (∀ j ∉ J.val, 0 < J.slack j x) ↔ changesAt A w ∧ 0 < J.slack i x := by
        constructor
        · intro hall
          refine ⟨⟨hi, fun k hk => ?_⟩, hall i i.prop⟩
          obtain ⟨hkJ, hki⟩ := (hA k).mp hk
          exact (hs ⟨k, hkJ⟩ (fun he => hki (congrArg Subtype.val he))).mp (hall k hkJ)
        · rintro ⟨hw, hx⟩ k hk
          by_cases hki : k = (i : ι)
          · simpa only [hki] using hx
          · exact (hs ⟨k, hk⟩ (fun he => hki (congrArg Subtype.val he))).mpr
              (hw.2 k ((hA k).mpr ⟨hk, hki⟩))
      have hh := hrest (fun j hj => (hsame j (huniq j hj)).1)
      have hh' := hrest (fun j hj => (hsame j (huniq j hj)).2)
      have hf : 0 < J.slack i h' ↔ ¬ 0 < J.slack i h :=
        pos_iff_not_of_mul_neg (hflip A hi)
      simp only [hh, hh', hf]
      change _ = wallContribution param h w A
      by_cases hc : changesAt A w <;> by_cases hpos : 0 < J.slack i h <;>
        simp [wallContribution, wallSign, wallForm, A, hc, hpos]
    · intro j _ hj
      exact ite_eq_right (fun h => huniq j hj h.1)
    · simp
  · have hn (j : I) : J.slack j w ≠ 0 := fun he => hex ⟨j, he⟩
    have he : (∀ j ∉ J.val, 0 < J.slack j h) ↔ (∀ j ∉ J.val, 0 < J.slack j h') := by
      exact ⟨fun ha j hj => (hsame ⟨j, hj⟩ (hn ⟨j, hj⟩)).2.mpr
          ((hsame ⟨j, hj⟩ (hn ⟨j, hj⟩)).1.mp (ha j hj)),
        fun ha j hj => (hsame ⟨j, hj⟩ (hn ⟨j, hj⟩)).1.mpr
          ((hsame ⟨j, hj⟩ (hn ⟨j, hj⟩)).2.mp (ha j hj))⟩
    simp only [he, sub_self]
    exact (Finset.sum_eq_zero (fun j _ => ite_eq_right (fun h => hn j h.1))).symm

omit [Fintype ι] in
private theorem changesAt_of_eq_support {A B : WallIndex v} {w : ι → ℝ}
    (hA : changesAt A w) (hK : wallSupport A = wallSupport B) : changesAt B w := by
  have h0 : wallForm v B w = 0 :=
    (mul_eq_zero.mp ((mul_wallForm_eq_of_support_eq hK w).trans hA.1)).resolve_left
      (circuitCoeff_ne_zero_of_support_eq hK)
  have hcoord (i : ι) (hi : i ∈ wallSupport A) : A.1.interpolate w (v i) = w i := by
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · have hw : A.1.slack A.2 w = 0 := hA.1
      rw [BasisIndex.slack_apply, sub_eq_zero] at hw
      exact hw.symm
    · exact A.1.interpolate_apply_of_mem _ hi'
  have he : A.1.interpolate w = B.1.interpolate w := by
    apply B.1.basis.ext
    intro i
    rw [B.1.basis_apply, B.1.interpolate_apply_of_mem _ i.prop]
    exact hcoord i (hK.symm ▸ (Finset.mem_insert_of_mem i.prop : (i : ι) ∈ wallSupport B))
  refine ⟨h0, fun i hi => ?_⟩
  rw [← hK] at hi
  simpa only [BasisIndex.slack_apply, he] using hA.2 i hi

private theorem wallSign_mul_abs {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    wallSign b * (↑|a| : ℂ) = wallSign (a * b) * (a : ℂ) := by
  rcases lt_or_gt_of_ne ha with hpa | hpa <;> rcases lt_or_gt_of_ne hb with hpb | hpb
  · simp [wallSign, not_lt_of_gt hpb, abs_of_neg hpa, mul_pos_of_neg_of_neg hpa hpb]
  · simp [wallSign, hpb, abs_of_neg hpa, (mul_neg_of_neg_of_pos hpa hpb).not_gt]
  · simp [wallSign, not_lt_of_gt hpb, abs_of_pos hpa, (mul_neg_of_pos_of_neg hpa hpb).not_gt]
  · simp [wallSign, hpb, abs_of_pos hpa, mul_pos hpa hpb]

private theorem sum_wallContribution_support_eq_zero (param : V →ₗ[ℝ] ℂ)
    (hp : ∀ i, v i ≠ 0 → param (v i) ≠ 0) (h w : ι → ℝ) (hreg : Regular (wallForm v) h)
    (hkeep : ∀ A : WallIndex v, v A.2 = 0 → wallForm v A w ≠ 0) (K : Finset ι) :
    ∑ B ∈ (Finset.univ : Finset (WallIndex v)).filter (fun B => wallSupport B = K),
      wallContribution param h w B = 0 := by
  let T := (Finset.univ : Finset (WallIndex v)).filter (fun B => wallSupport B = K)
  by_cases hex : ∃ A ∈ T, changesAt A w
  · obtain ⟨A, hAT, hA⟩ := hex
    have hAK : wallSupport A = K := (Finset.mem_filter.mp hAT).2
    have hproj (i : ι) (hi : i ∈ K) : param (v i) ≠ 0 := by
      apply hp i
      rw [← hAK] at hi
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · exact fun hz => hkeep A hz hA.1
      · exact A.1.prop.1.ne_zero ⟨i, hi'⟩
    let C : ℂ := wallSign (wallForm v A h) *
      (gramVolume (fun j : A.1.val => v j) : ℂ) / ∏ j ∈ K, param (v j)
    have hterm (B : WallIndex v) (hBT : B ∈ T) :
        wallContribution param h w B = C * (circuitCoeff A B.2 : ℂ) * param (v B.2) := by
      have hBK : wallSupport B = K := (Finset.mem_filter.mp hBT).2
      have hAB := hAK.trans hBK.symm
      simp only [wallContribution, changesAt_of_eq_support hA hAB, ite_true]
      rw [weight_eq_of_support_eq param hAB (by simpa only [hAK] using hproj), hAK]
      have hs := wallSign_mul_abs (circuitCoeff_ne_zero_of_support_eq hAB) (hreg B)
      rw [mul_wallForm_eq_of_support_eq hAB] at hs
      unfold C
      calc
        _ = (gramVolume (fun j : A.1.val => v j) : ℂ) / (∏ j ∈ K, param (v j)) *
            (wallSign (wallForm v B h) * (↑|circuitCoeff A B.2| : ℂ)) * param (v B.2) := by ring
        _ = _ := by rw [hs]; ring
    have hsum : ∑ B ∈ T, wallContribution param h w B =
        ∑ i ∈ K.filter (fun i => circuitCoeff A i ≠ 0), C * (circuitCoeff A i : ℂ) * param (v i) := by
      apply Finset.sum_bij (fun B _ => (B.2 : ι))
      · intro B hBT
        have hBK := (Finset.mem_filter.mp hBT).2
        exact Finset.mem_filter.mpr ⟨hBK ▸ (Finset.mem_insert_self _ _ : (B.2 : ι) ∈ wallSupport B),
          circuitCoeff_ne_zero_of_support_eq (hAK.trans hBK.symm)⟩
      · intro B hBT D hDT hi
        exact eq_of_support_eq_of_index_eq ((Finset.mem_filter.mp hBT).2.trans
          (Finset.mem_filter.mp hDT).2.symm) hi
      · intro i hi
        obtain ⟨B, hB, hBi⟩ := exists_wallIndex_of_circuitCoeff_ne_zero A
          (hAK.symm ▸ (Finset.mem_filter.mp hi).1) (Finset.mem_filter.mp hi).2
        exact ⟨B, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB.trans hAK⟩, hBi⟩
      · exact hterm
    change (∑ B ∈ T, _) = 0
    rw [hsum, Finset.sum_filter]
    have hL : ∑ i ∈ K, (circuitCoeff A i : ℂ) * param (v i) = 0 := by
      have he := congrArg param (sum_circuitCoeff_smul A)
      simpa only [hAK, map_sum, map_smul, Complex.real_smul, map_zero] using he
    calc
      _ = ∑ i ∈ K, C * ((circuitCoeff A i : ℂ) * param (v i)) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hc : circuitCoeff A i = 0 <;> simp [hc, mul_assoc]
      _ = 0 := by rw [← Finset.mul_sum, hL, mul_zero]
  · exact Finset.sum_eq_zero fun B hB => ite_eq_right (fun hc => hex ⟨B, hB, hc⟩)

/-- The vertex sum is unchanged between regular offsets when each zero normal keeps its sign. -/
theorem vertexSum_eq_of_regular (param : V →ₗ[ℝ] ℂ)
    (hp : ∀ i, v i ≠ 0 → param (v i) ≠ 0) {h h' : ι → ℝ}
    (hh : Regular (wallForm v) h) (hh' : Regular (wallForm v) h')
    (hkeep : ∀ A : WallIndex v, v A.2 = 0 → 0 < h A.2 * h' A.2) :
    vertexSum v param h = vertexSum v param h' := by
  let keep (A : WallIndex v) : Prop := v A.2 = 0
  have hprotect (A : WallIndex v) (hA : keep A) : 0 < wallForm v A h * wallForm v A h' := by
    simpa only [wallForm, slack_of_normal_eq_zero A.1 hA] using hkeep A hA
  have hgal := reflTransGen_chamberStep (wallForm v) keep hh hh' hprotect
  have hstep (x y : ι → ℝ) (hstep : ChamberStep (wallForm v) keep x y) :
      vertexSum v param x = vertexSum v param y := by
    rcases hstep with hsame | hwall
    · apply Finset.sum_congr rfl
      intro J _
      have he (j : ι) (hj : j ∉ J.val) : 0 < J.slack j x ↔ 0 < J.slack j y :=
        pos_iff_of_mul_pos (hsame ⟨J, j, hj⟩)
      have he' : (∀ j ∉ J.val, 0 < J.slack j x) ↔ (∀ j ∉ J.val, 0 < J.slack j y) :=
        forall_congr' (fun j => forall_congr' (he j))
      simp only [he']
    · obtain ⟨hx, _, w, _, hf, hfix, hprop, hkeep'⟩ := hwall
      apply sub_eq_zero.mp
      unfold vertexSum
      rw [← Finset.sum_sub_distrib]
      simp_rw [contribution_eq_sum_wall param _ hf hfix hprop, ← Fintype.sum_sigma']
      rw [← Finset.sum_fiberwise (Finset.univ : Finset (WallIndex v)) wallSupport]
      exact Finset.sum_eq_zero fun K _ =>
        sum_wallContribution_support_eq_zero param hp x w hx hkeep' K
  have hc (y : ι → ℝ) (hy : Relation.ReflTransGen (ChamberStep (wallForm v) keep) h y) :
      vertexSum v param h = vertexSum v param y := by
    induction hy with
    | refl => rfl
    | tail _ hxy ih => exact ih.trans (hstep _ _ hxy)
  exact hc h' hgal

/-- If the nonzero normals admit no common strictly positive functional, the weighted sum
    at regular offsets vanishes. -/
theorem vertexSum_eq_zero_of_no_strict_direction (param : V →ₗ[ℝ] ℂ)
    (hp : ∀ i, v i ≠ 0 → param (v i) ≠ 0) {h : ι → ℝ}
    (hh : Regular (wallForm v) h)
    (hn : ¬ ∃ f : Module.Dual ℝ V, ∀ i, v i ≠ 0 → 0 < f (v i)) :
    vertexSum v param h = 0 := by
  let y (i : ι) : ℝ := if v i = 0 then h i else -1
  let f (a : WallIndex v ⊕ ι) : Module.Dual ℝ (ι → ℝ) :=
    Sum.elim (wallForm v) LinearMap.proj a
  have hf (i : WallIndex v ⊕ ι) : f i ≠ 0 := by
    rcases i with A | i
    · exact wallForm_ne_zero v A
    · intro he
      have he' := congrArg (fun l : Module.Dual ℝ (ι → ℝ) => l (Pi.single i 1)) he
      simp [f] at he'
  obtain ⟨z, hz, hs⟩ := exists_regular_preserving_signs f hf y
  have hsign (i : ι) (hi : y i ≠ 0) : 0 < y i * z i := hs (.inr i) hi
  have hsame (A : WallIndex v) (hA : v A.2 = 0) : 0 < h A.2 * z A.2 := by
    have hne : h A.2 ≠ 0 := by simpa only [wallForm, slack_of_normal_eq_zero A.1 hA] using hh A
    have he : y A.2 = h A.2 := ite_eq_left hA
    exact he ▸ hsign A.2 (he ▸ hne)
  rw [vertexSum_eq_of_regular param hp hh (fun A => hz (.inl A)) hsame]
  refine Finset.sum_eq_zero fun J _ => ite_eq_right (fun hJ => hn ⟨-J.interpolate z, fun i hi => ?_⟩)
  have hy : y i = -1 := ite_eq_right hi
  have hz' : z i < 0 := by
    have ht := hsign i (hy ▸ neg_ne_zero.mpr one_ne_zero)
    rw [hy] at ht
    linarith
  have he : 0 ≤ J.slack i z := by
    by_cases hmem : i ∈ J.val
    · rw [J.slack_apply_of_mem hmem]
    · exact (hJ i hmem).le
  rw [J.slack_apply] at he
  simp only [LinearMap.neg_apply]
  linarith

end Langlands.LinearAlgebra.AffineVertexWeights
