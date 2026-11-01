import Langlands.Analysis.CoordinateScalarFrozenDerivativeEstimateStatement
import Langlands.Analysis.OrderedDerivativeFamilyLeibnizProof
import Langlands.Analysis.SmoothIteratedFDerivSymm

/-! # Proof of the differentiated frozen principal estimate -/

noncomputable section
open scoped BigOperators ContDiff Topology
open Function Filter
set_option autoImplicit false

namespace Langlands.Analysis

universe uA uE

variable {A : Type uA} [Fintype A]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

private abbrev scalarTensorNorm (v : A → E) (p : ℕ) (f : E → ℂ) (x : E) : ℝ :=
  orderedDerivativeFamilyNorm v p (fun _ : Unit => f) x

private theorem scalarTensorNorm_eq_sqrt (v : A → E) (p : ℕ) (f : E → ℂ) (x : E) :
    scalarTensorNorm v p f x =
      Real.sqrt (∑ w : Fin p → A, ‖iteratedFDeriv ℝ p f x (v ∘ w)‖ ^ 2) := by
  simp [scalarTensorNorm, orderedDerivativeFamilyNorm_eq_sqrt]

private theorem scalarTensorNorm_nonneg (v : A → E) (p : ℕ) (f : E → ℂ) (x : E) :
    0 ≤ scalarTensorNorm v p f x :=
  orderedDerivativeFamilyNorm_nonneg _ _ _ _

private theorem scalarTensorNorm_zero (v : A → E) (f : E → ℂ) (x : E) :
    scalarTensorNorm v 0 f x = ‖f x‖ := by
  simp [scalarTensorNorm_eq_sqrt]

private theorem scalarTensorNorm_neg (v : A → E) (p : ℕ) (f : E → ℂ) (x : E) :
    scalarTensorNorm v p (fun y => -f y) x = scalarTensorNorm v p f x := by
  simp [scalarTensorNorm_eq_sqrt, ← Pi.neg_def, iteratedFDeriv_neg_apply]

private theorem scalarTensorNorm_const_sub_succ
    (v : A → E) (p : ℕ) (a : ℂ) {f : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ (p + 1) f x) :
    scalarTensorNorm v (p + 1) (fun y => a - f y) x =
      scalarTensorNorm v (p + 1) f x := by
  simp only [scalarTensorNorm_eq_sqrt]
  congr 1
  apply Finset.sum_congr rfl
  intro w hw
  rw [fun_iteratedFDeriv_sub_apply contDiffAt_const hf, iteratedFDeriv_succ_const]
  simp

private theorem scalarTensorNorm_add_le
    (v : A → E) (p : ℕ) (f g : E → ℂ) (x : E)
    (hf : ContDiffAt ℝ p f x) (hg : ContDiffAt ℝ p g x) :
    scalarTensorNorm v p (fun y => f y + g y) x ≤
      scalarTensorNorm v p f x + scalarTensorNorm v p g x :=
  orderedDerivativeFamilyNorm_add_le v p _ _ x (fun _ => hf) (fun _ => hg)

private theorem scalarTensorNorm_sum_le
    {I : Type*} (s : Finset I) (v : A → E) (p : ℕ) (f : I → E → ℂ) (x : E)
    (hf : ∀ i ∈ s, ContDiffAt ℝ p (f i) x) :
    scalarTensorNorm v p (fun y => ∑ i ∈ s, f i y) x ≤
      ∑ i ∈ s, scalarTensorNorm v p (f i) x := by
  unfold scalarTensorNorm orderedDerivativeFamilyNorm finiteFamilyL2Norm
  simp_rw [iteratedFDeriv_fun_sum_apply hf, sum_apply]
  have hsum :
      (fun iw : Unit × (Fin p → A) =>
        ∑ i ∈ s, iteratedFDeriv ℝ p (f i) x (v ∘ iw.2)) =
        ∑ i ∈ s, fun iw : Unit × (Fin p → A) =>
          iteratedFDeriv ℝ p (f i) x (v ∘ iw.2) := by
    funext iw
    simp
  rw [hsum, WithLp.toLp_sum]
  exact norm_sum_le _ _

private theorem scalarTensorNorm_mul_le
    (v : A → E) (p : ℕ) (f g : E → ℂ) (S : Set E) (hS : IsOpen S)
    (hf : ContDiffOn ℝ ∞ f S) (hg : ContDiffOn ℝ ∞ g S) (x : E) (hx : x ∈ S) :
    scalarTensorNorm v p (fun y => f y * g y) x ≤
      ∑ j ∈ Finset.range (p + 1), (p.choose j : ℝ) *
        scalarTensorNorm v j f x * scalarTensorNorm v (p - j) g x := by
  have h := orderedDerivativeFamilyLeibniz (I := Unit) (J := Unit) v
    (ContinuousLinearMap.mul ℝ ℂ) p (fun _ => f) (fun _ => g) S hS
    (fun _ => hf) (fun _ => hg) x hx
  simpa [orderedDerivativeFamilyNorm_eq_sqrt, scalarTensorNorm_eq_sqrt,
    ContinuousLinearMap.opNorm_mul] using h

private theorem scalarTensorNorm_lineDeriv_le
    (v : A → E) (p k : ℕ) (u : E → ℂ) (S : Set E) (hS : IsOpen S)
    (hu : ContDiffOn ℝ ∞ u S) (x : E) (hx : x ∈ S) (w : Fin k → A) :
    scalarTensorNorm v p (fun y => iteratedFDeriv ℝ k u y (v ∘ w)) x ≤
      scalarTensorNorm v (p + k) u x := by
  simp only [scalarTensorNorm_eq_sqrt]
  apply Real.sqrt_le_sqrt
  have happ (z : Fin p → A) :
      iteratedFDeriv ℝ p (fun y => iteratedFDeriv ℝ k u y (v ∘ w)) x (v ∘ z) =
        iteratedFDeriv ℝ (p + k) u x (v ∘ Fin.append z w) := by
    rw [← iteratedFDeriv_append_of_contDiffOn hu hS hx (by simp)]
    congr 1
    funext i
    induction i using Fin.addCases with
    | left i => simp
    | right i => simp
  simp_rw [happ]
  calc
    _ ≤ ∑ z : Fin p → A, ∑ w' : Fin k → A,
        ‖iteratedFDeriv ℝ (p + k) u x (v ∘ Fin.append z w')‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro z hz
      exact Finset.single_le_sum
        (f := fun w' : Fin k → A =>
          ‖iteratedFDeriv ℝ (p + k) u x (v ∘ Fin.append z w')‖ ^ 2)
        (fun w' _ => sq_nonneg _) (Finset.mem_univ w)
    _ = _ := by
      rw [← Fintype.sum_prod_type']
      exact (Fin.appendEquiv p k).sum_comp
        (fun W => ‖iteratedFDeriv ℝ (p + k) u x (v ∘ W)‖ ^ 2)

private theorem scalarTensorNorm_coeff_lineDeriv_le
    (v : A → E) (p k : ℕ) (a u : E → ℂ) (S : Set E) (hS : IsOpen S)
    (ha : ContDiffOn ℝ ∞ a S) (hu : ContDiffOn ℝ ∞ u S)
    (x : E) (hx : x ∈ S) (w : Fin k → A) :
    scalarTensorNorm v p (fun y => a y * iteratedFDeriv ℝ k u y (v ∘ w)) x ≤
      ∑ j ∈ Finset.range (p + 1), (p.choose j : ℝ) *
        scalarTensorNorm v j a x * scalarTensorNorm v (p - j + k) u x := by
  have hline := contDiffOn_infty_iteratedLineDeriv hu hS (v ∘ w)
  calc
    _ ≤ ∑ j ∈ Finset.range (p + 1), (p.choose j : ℝ) *
        scalarTensorNorm v j a x *
          scalarTensorNorm v (p - j) (fun y => iteratedFDeriv ℝ k u y (v ∘ w)) x :=
      scalarTensorNorm_mul_le v p a _ S hS ha hline x hx
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left
        (scalarTensorNorm_lineDeriv_le v (p - j) k u S hS hu x hx w)
        (mul_nonneg (Nat.cast_nonneg _) (scalarTensorNorm_nonneg _ _ _ _))

private theorem scalarTensorNorm_frozen_coeff_lineDeriv_le
    (v : A → E) (p k : ℕ) (a u : E → ℂ) (S : Set E) (hS : IsOpen S)
    (ha : ContDiffOn ℝ ∞ a S) (hu : ContDiffOn ℝ ∞ u S)
    (x₀ x : E) (hx : x ∈ S) (w : Fin k → A) :
    scalarTensorNorm v p
        (fun y => (a x₀ - a y) * iteratedFDeriv ℝ k u y (v ∘ w)) x ≤
      ‖a x₀ - a x‖ * scalarTensorNorm v (p + k) u x +
        ∑ j ∈ Finset.range p, (p.choose (j + 1) : ℝ) *
          scalarTensorNorm v (j + 1) a x *
            scalarTensorNorm v (p - (j + 1) + k) u x := by
  have h := scalarTensorNorm_coeff_lineDeriv_le v p k (fun y => a x₀ - a y)
    u S hS (contDiffOn_const.sub ha) hu x hx w
  rw [Finset.sum_range_succ'] at h
  simpa [scalarTensorNorm_zero, scalarTensorNorm_const_sub_succ v _ _
    ((ha.contDiffAt (hS.mem_nhds hx)).of_le (by simp)), add_comm] using h

/-- The complete ordered tensor of the frozen action is controlled by the actual
full action and the exact lower-order coefficient products. -/
theorem coordinateScalarFrozenDerivativeEstimate (d r : ℕ) :
    CoordinateScalarFrozenDerivativeEstimateStatement E d r := by
  intro D
  dsimp only
  intro S hS hcoeff u hu x₀ p x hx
  let v : Fin d → E := fun i => D.basis i
  let f : (k : Fin (r + 1)) → (Fin k.val → Fin d) → E → ℂ :=
    fun k w y => D.coefficient k w y * iteratedFDeriv ℝ k.val u y (v ∘ w)
  let V : (Fin r → Fin d) → E → ℂ := fun w y =>
    (D.coefficient (Fin.last r) w x₀ - D.coefficient (Fin.last r) w y) *
      iteratedFDeriv ℝ r u y (v ∘ w)
  let H : E → ℂ := fun y => ∑ w : Fin r → Fin d, V w y
  let L : E → ℂ := fun y => ∑ k : Fin r, ∑ w : Fin k.val → Fin d, f k.castSucc w y
  have hf (k : Fin (r + 1)) (w : Fin k.val → Fin d) :
      ContDiffOn ℝ ∞ (f k w) S :=
    (hcoeff k w).mul (contDiffOn_infty_iteratedLineDeriv hu hS (v ∘ w))
  have hV (w : Fin r → Fin d) : ContDiffOn ℝ ∞ (V w) S :=
    (contDiffOn_const.sub (hcoeff (Fin.last r) w)).mul
      (contDiffOn_infty_iteratedLineDeriv hu hS (v ∘ w))
  have hH : ContDiffOn ℝ ∞ H S := ContDiffOn.sum (fun w _ => hV w)
  have hL : ContDiffOn ℝ ∞ L S :=
    ContDiffOn.sum (fun k _ => ContDiffOn.sum (fun w _ => hf k.castSucc w))
  have haction : ContDiffOn ℝ ∞ (D.action u) S :=
    ContDiffOn.sum (fun k _ => ContDiffOn.sum (fun w _ => hf k w))
  have hat {g : E → ℂ} (hg : ContDiffOn ℝ ∞ g S) : ContDiffAt ℝ p g x :=
    (hg.contDiffAt (hS.mem_nhds hx)).of_le (by simp)
  have hsplit (y : E) :
      D.action u y = L y +
        ∑ w : Fin r → Fin d, D.coefficient (Fin.last r) w y *
          iteratedFDeriv ℝ r u y (v ∘ w) := by
    exact Fin.sum_univ_castSucc _
  have hdecomp :
      (fun y => ∑ w : Fin r → Fin d, D.coefficient (Fin.last r) w x₀ *
        iteratedFDeriv ℝ r u y (v ∘ w)) =
      (fun y => (D.action u y + H y) + -L y) := by
    funext y
    rw [hsplit]
    dsimp only [H, V]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    ring
  have hHsum : scalarTensorNorm v p H x ≤
      ∑ w : Fin r → Fin d, scalarTensorNorm v p (V w) x :=
    scalarTensorNorm_sum_le Finset.univ v p V x (fun w _ => hat (hV w))
  have hLsum : scalarTensorNorm v p L x ≤
      ∑ k : Fin r, ∑ w : Fin k.val → Fin d, scalarTensorNorm v p (f k.castSucc w) x := by
    apply (scalarTensorNorm_sum_le Finset.univ v p
      (fun k : Fin r => fun y => ∑ w : Fin k.val → Fin d, f k.castSucc w y) x
      (fun k _ => hat (ContDiffOn.sum (fun w _ => hf k.castSucc w)))).trans
    apply Finset.sum_le_sum
    intro k hk
    exact scalarTensorNorm_sum_le Finset.univ v p _ x (fun w _ => hat (hf k.castSucc w))
  have htop (w : Fin r → Fin d) :
      scalarTensorNorm v p (V w) x ≤
        ‖D.coefficient (Fin.last r) w x₀ - D.coefficient (Fin.last r) w x‖ *
            scalarTensorNorm v (p + r) u x +
          ∑ j ∈ Finset.range p, (p.choose (j + 1) : ℝ) *
            scalarTensorNorm v (j + 1) (D.coefficient (Fin.last r) w) x *
              scalarTensorNorm v (p - (j + 1) + r) u x :=
    scalarTensorNorm_frozen_coeff_lineDeriv_le v p r _ u S hS
      (hcoeff (Fin.last r) w) hu x₀ x hx w
  have hlower (k : Fin r) (w : Fin k.val → Fin d) :
      scalarTensorNorm v p (f k.castSucc w) x ≤
        ∑ j ∈ Finset.range (p + 1), (p.choose j : ℝ) *
          scalarTensorNorm v j (D.coefficient k.castSucc w) x *
            scalarTensorNorm v (p - j + k.val) u x :=
    scalarTensorNorm_coeff_lineDeriv_le v p k.val _ u S hS
      (hcoeff k.castSucc w) hu x hx w
  change scalarTensorNorm v p _ x ≤ _
  rw [hdecomp]
  calc
    _ ≤ scalarTensorNorm v p (fun y => D.action u y + H y) x +
        scalarTensorNorm v p (fun y => -L y) x :=
      scalarTensorNorm_add_le v p _ _ x (hat (haction.add hH)) (hat hL.neg)
    _ ≤ (scalarTensorNorm v p (D.action u) x + scalarTensorNorm v p H x) +
        scalarTensorNorm v p L x := by
      rw [scalarTensorNorm_neg]
      exact add_le_add
        (scalarTensorNorm_add_le v p _ _ x (hat haction) (hat hH)) le_rfl
    _ ≤ (scalarTensorNorm v p (D.action u) x +
        ∑ w : Fin r → Fin d, scalarTensorNorm v p (V w) x) +
        ∑ k : Fin r, ∑ w : Fin k.val → Fin d, scalarTensorNorm v p (f k.castSucc w) x :=
      add_le_add (add_le_add le_rfl hHsum) hLsum
    _ ≤ (scalarTensorNorm v p (D.action u) x +
        ∑ w : Fin r → Fin d,
          (‖D.coefficient (Fin.last r) w x₀ - D.coefficient (Fin.last r) w x‖ *
              scalarTensorNorm v (p + r) u x +
            ∑ j ∈ Finset.range p, (p.choose (j + 1) : ℝ) *
              scalarTensorNorm v (j + 1) (D.coefficient (Fin.last r) w) x *
                scalarTensorNorm v (p - (j + 1) + r) u x)) +
        ∑ k : Fin r, ∑ w : Fin k.val → Fin d,
          ∑ j ∈ Finset.range (p + 1), (p.choose j : ℝ) *
            scalarTensorNorm v j (D.coefficient k.castSucc w) x *
              scalarTensorNorm v (p - j + k.val) u x := by
      exact add_le_add
        (add_le_add le_rfl (Finset.sum_le_sum (fun w _ => htop w)))
        (Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun w _ => hlower k w)))
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      simp only [scalarTensorNorm, v, add_assoc]

end Langlands.Analysis
