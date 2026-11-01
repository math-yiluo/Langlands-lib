import Langlands.Analysis.OrderedDerivativeFamilyLeibnizStatement

/-! # Proof of the ordered derivative family Leibniz bound -/

noncomputable section
open scoped BigOperators ContDiff Topology
open Function Filter
set_option autoImplicit false

namespace Langlands.Analysis

universe uA uI uJ uE uF uG uH

variable {A : Type uA} [Fintype A]
  {I : Type uI} [Fintype I] {J : Type uJ} [Fintype J]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type uG} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {H : Type uH} [NormedAddCommGroup H] [NormedSpace ℝ H]

omit [NormedSpace ℝ F] in
private theorem finiteFamilyL2Norm_sq (f : I → F) :
    finiteFamilyL2Norm f ^ 2 = ∑ i, ‖f i‖ ^ 2 := by
  rw [finiteFamilyL2Norm_eq_sqrt, Real.sq_sqrt]
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

private theorem finiteFamilyL2Norm_bilinear_le
    (B : F →L[ℝ] G →L[ℝ] H) (f : I → F) (g : J → G) :
    finiteFamilyL2Norm (fun ij : I × J => B (f ij.1) (g ij.2)) ≤
      ‖B‖ * finiteFamilyL2Norm f * finiteFamilyL2Norm g := by
  have hsq :
      finiteFamilyL2Norm (fun ij : I × J => B (f ij.1) (g ij.2)) ^ 2 ≤
        (‖B‖ * finiteFamilyL2Norm f * finiteFamilyL2Norm g) ^ 2 := by
    rw [finiteFamilyL2Norm_sq, Fintype.sum_prod_type]
    calc
      (∑ i, ∑ j, ‖B (f i) (g j)‖ ^ 2) ≤
          ∑ i, ∑ j, (‖B‖ * ‖f i‖ * ‖g j‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (B.le_opNorm₂ _ _)
      _ = (‖B‖ * finiteFamilyL2Norm f * finiteFamilyL2Norm g) ^ 2 := by
        simp only [mul_pow, finiteFamilyL2Norm_sq]
        simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
        exact Finset.sum_comm
  have hnonneg :
      0 ≤ ‖B‖ * finiteFamilyL2Norm f * finiteFamilyL2Norm g :=
    mul_nonneg (mul_nonneg (norm_nonneg B) (finiteFamilyL2Norm_nonneg f))
      (finiteFamilyL2Norm_nonneg _)
  exact (sq_le_sq₀ (finiteFamilyL2Norm_nonneg _) hnonneg).1 hsq

private theorem orderedDerivativeFamilyNorm_congr_eventually
    (v : A → E) (p : ℕ) {f g : I → E → F} {x : E}
    (h : ∀ i, f i =ᶠ[𝓝 x] g i) :
    orderedDerivativeFamilyNorm v p f x = orderedDerivativeFamilyNorm v p g x := by
  unfold orderedDerivativeFamilyNorm
  apply finiteFamilyL2Norm_congr
  intro iw
  rw [((h iw.1).iteratedFDeriv ℝ p).eq_of_nhds]

private theorem contDiffOn_fixed_lineDeriv
    {f : E → F} {S : Set E} (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ f S) (a : E) :
    ContDiffOn ℝ ∞ (fun y => fderiv ℝ f y a) S := by
  exact (hf.fderiv_of_isOpen hS (by simp)).clm_apply contDiffOn_const

private theorem orderedDerivativeFamilyNorm_prod_swap
    (v : A → E) (p : ℕ) (f : A × (I × J) → E → F) (x : E) :
    orderedDerivativeFamilyNorm v p f x =
      orderedDerivativeFamilyNorm v p
        (fun iaj : I × (A × J) => f (iaj.2.1, (iaj.1, iaj.2.2))) x := by
  simp only [orderedDerivativeFamilyNorm_eq_sqrt, Fintype.sum_prod_type]
  congr 1
  exact Finset.sum_comm

private theorem orderedDerivativeFamilyLeibniz_aux
    {I : Type (max uA uI)} [Fintype I] {J : Type (max uA uJ)} [Fintype J]
    (v : A → E) (B : F →L[ℝ] G →L[ℝ] H) (p : ℕ)
    (f : I → E → F) (g : J → E → G) (S : Set E) (hS : IsOpen S)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) S) (hg : ∀ j, ContDiffOn ℝ ∞ (g j) S)
    (x : E) (hx : x ∈ S) :
    orderedDerivativeFamilyNorm v p
        (fun ij : I × J => fun y => B (f ij.1 y) (g ij.2 y)) x ≤
      ‖B‖ * ∑ l ∈ Finset.range (p + 1), (p.choose l : ℝ) *
        orderedDerivativeFamilyNorm v l f x *
        orderedDerivativeFamilyNorm v (p - l) g x := by
  induction p generalizing I J with
  | zero =>
    simpa [orderedDerivativeFamilyNorm_zero, mul_assoc] using
      finiteFamilyL2Norm_bilinear_le B (fun i => f i x) (fun j => g j x)
  | succ p IH =>
    let df : A × I → E → F := fun ai y => fderiv ℝ (f ai.2) y (v ai.1)
    let dg : A × J → E → G := fun aj y => fderiv ℝ (g aj.2) y (v aj.1)
    have hdf : ∀ ai, ContDiffOn ℝ ∞ (df ai) S := fun ai =>
      contDiffOn_fixed_lineDeriv hS (hf ai.2) (v ai.1)
    have hdg : ∀ aj, ContDiffOn ℝ ∞ (dg aj) S := fun aj =>
      contDiffOn_fixed_lineDeriv hS (hg aj.2) (v aj.1)
    have hnf : ∀ l, orderedDerivativeFamilyNorm v l df x =
        orderedDerivativeFamilyNorm v (l + 1) f x := by
      intro l
      exact orderedDerivativeFamilyNorm_lineDeriv v l f x
        (fun i => ((hf i).contDiffAt (hS.mem_nhds hx)).of_le (by simp))
    have hng : ∀ l, orderedDerivativeFamilyNorm v l dg x =
        orderedDerivativeFamilyNorm v (l + 1) g x := by
      intro l
      exact orderedDerivativeFamilyNorm_lineDeriv v l g x
        (fun j => ((hg j).contDiffAt (hS.mem_nhds hx)).of_le (by simp))
    let R : A × (I × J) → E → H :=
      fun aij y => B (f aij.2.1 y) (dg (aij.1, aij.2.2) y)
    let L : A × (I × J) → E → H :=
      fun aij y => B (df (aij.1, aij.2.1) y) (g aij.2.2 y)
    have hR : ∀ aij, ContDiffOn ℝ ∞ (R aij) S := fun aij =>
      B.isBoundedBilinearMap.contDiff.comp₂_contDiffOn
        (hf aij.2.1) (hdg (aij.1, aij.2.2))
    have hL : ∀ aij, ContDiffOn ℝ ∞ (L aij) S := fun aij =>
      B.isBoundedBilinearMap.contDiff.comp₂_contDiffOn
        (hdf (aij.1, aij.2.1)) (hg aij.2.2)
    have I1 : orderedDerivativeFamilyNorm v p R x ≤
        ‖B‖ * ∑ l ∈ Finset.range (p + 1), (p.choose l : ℝ) *
          orderedDerivativeFamilyNorm v l f x *
          orderedDerivativeFamilyNorm v (p + 1 - l) g x := by
      rw [orderedDerivativeFamilyNorm_prod_swap]
      calc
        _ ≤ ‖B‖ * ∑ l ∈ Finset.range (p + 1), (p.choose l : ℝ) *
            orderedDerivativeFamilyNorm v l f x *
            orderedDerivativeFamilyNorm v (p - l) dg x :=
          IH f dg hf hdg
        _ = _ := by
          congr 1
          apply Finset.sum_congr rfl
          intro l hl
          rw [hng, Nat.succ_sub (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl))]
    have I2 : orderedDerivativeFamilyNorm v p L x ≤
        ‖B‖ * ∑ l ∈ Finset.range (p + 1), (p.choose l : ℝ) *
          orderedDerivativeFamilyNorm v (l + 1) f x *
          orderedDerivativeFamilyNorm v (p - l) g x := by
      have h := IH df g hdf hg
      simp_rw [hnf] at h
      convert h using 1
      simp only [orderedDerivativeFamilyNorm_eq_sqrt, Fintype.sum_prod_type, L]
    have hprod : ∀ ij : I × J,
        ContDiffOn ℝ ∞ (fun y => B (f ij.1 y) (g ij.2 y)) S := fun ij =>
      B.isBoundedBilinearMap.contDiff.comp₂_contDiffOn (hf ij.1) (hg ij.2)
    have hsplit :
        orderedDerivativeFamilyNorm v p
            (fun aij : A × (I × J) => fun y =>
              fderiv ℝ (fun z => B (f aij.2.1 z) (g aij.2.2 z)) y (v aij.1)) x =
          orderedDerivativeFamilyNorm v p (fun aij y => R aij y + L aij y) x := by
      apply orderedDerivativeFamilyNorm_congr_eventually
      intro aij
      filter_upwards [hS.mem_nhds hx] with y hy
      dsimp [R, L, df, dg]
      rw [B.fderiv_of_bilinear
        (((hf aij.2.1).contDiffAt (hS.mem_nhds hy)).differentiableAt (by simp))
        (((hg aij.2.2).contDiffAt (hS.mem_nhds hy)).differentiableAt (by simp))]
      rfl
    calc
      _ = orderedDerivativeFamilyNorm v p
          (fun aij : A × (I × J) => fun y =>
            fderiv ℝ (fun z => B (f aij.2.1 z) (g aij.2.2 z)) y (v aij.1)) x :=
        (orderedDerivativeFamilyNorm_lineDeriv v p _ x
          (fun ij => ((hprod ij).contDiffAt (hS.mem_nhds hx)).of_le (by simp))).symm
      _ = orderedDerivativeFamilyNorm v p (fun aij y => R aij y + L aij y) x := hsplit
      _ ≤ orderedDerivativeFamilyNorm v p R x + orderedDerivativeFamilyNorm v p L x :=
        orderedDerivativeFamilyNorm_add_le v p R L x
          (fun aij => ((hR aij).contDiffAt (hS.mem_nhds hx)).of_le (by simp))
          (fun aij => ((hL aij).contDiffAt (hS.mem_nhds hx)).of_le (by simp))
      _ ≤ _ := add_le_add I1 I2
      _ = _ := by
        rw [← mul_add]
        congr 1
        simp_rw [mul_assoc]
        exact (Finset.sum_choose_succ_mul
          (fun i j => orderedDerivativeFamilyNorm v i f x *
            orderedDerivativeFamilyNorm v j g x) p).symm

/-- The dimension-sharp binomial Leibniz estimate for every complete ordered
derivative family, with independent universes for both finite families. -/
theorem orderedDerivativeFamilyLeibniz
    (v : A → E) (B : F →L[ℝ] G →L[ℝ] H) :
    OrderedDerivativeFamilyLeibnizStatement (I := I) (J := J) v B := by
  intro p f g S hS hf hg x hx
  let eI : ULift.{uA} I ≃ I := Equiv.ulift
  let eJ : ULift.{uA} J ≃ J := Equiv.ulift
  let fl : ULift.{uA} I → E → F := fun i => f (eI i)
  let gl : ULift.{uA} J → E → G := fun j => g (eJ j)
  have h := orderedDerivativeFamilyLeibniz_aux v B p fl gl S hS
    (fun i => hf (eI i)) (fun j => hg (eJ j)) x hx
  have hnf : ∀ l, orderedDerivativeFamilyNorm v l fl x =
      orderedDerivativeFamilyNorm v l f x := fun l =>
    orderedDerivativeFamilyNorm_reindex eI v l f x
  have hng : ∀ l, orderedDerivativeFamilyNorm v l gl x =
      orderedDerivativeFamilyNorm v l g x := fun l =>
    orderedDerivativeFamilyNorm_reindex eJ v l g x
  simp_rw [hnf, hng] at h
  convert h using 1
  exact (orderedDerivativeFamilyNorm_reindex (Equiv.prodCongr eI eJ) v p
    (fun ij : I × J => fun y => B (f ij.1 y) (g ij.2 y)) x).symm

end Langlands.Analysis
