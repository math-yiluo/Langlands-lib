import Langlands.Analysis.CanonicalScalarWeightedFactorialBoundsStatement
import Langlands.Analysis.CoordinateScalarFrozenDerivativeEstimateProof
import Langlands.Analysis.AnalyticFactorialDerivativeBounds
import Langlands.Analysis.CoordinateScalarLocalEllipticityProof
import Langlands.Analysis.ConstantCoefficientEllipticL2EstimateProof

/-! # Actual weighted factorial derivative bounds -/

noncomputable section
open scoped BigOperators ContDiff ENNReal Topology
open Function Filter MeasureTheory Metric Set
set_option autoImplicit false

namespace Langlands.Analysis

universe uI uE uF

/-- A dimension loss confined to the order of the coefficient derivative.
No smoothness is needed for this finite-dimensional norm comparison. -/
private theorem singletonTensorNorm_le_card_pow
    {I : Type uI} [Fintype I]
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (v : I → E) (hv : ∀ i, ‖v i‖ ≤ 1) (j : ℕ) (f : E → F) (x : E) :
    orderedDerivativeFamilyNorm v j (fun _ : Unit => f) x ≤
      (Fintype.card I : ℝ) ^ j * ‖iteratedFDeriv ℝ j f x‖ := by
  classical
  have hsq :
      (∑ w : Fin j → I, ‖iteratedFDeriv ℝ j f x (v ∘ w)‖ ^ 2) ≤
        (∑ w : Fin j → I, ‖iteratedFDeriv ℝ j f x (v ∘ w)‖) ^ 2 := by
    simpa using Finset.sum_sq_le_sq_sum_of_nonneg
      (s := Finset.univ)
      (f := fun w : Fin j → I => ‖iteratedFDeriv ℝ j f x (v ∘ w)‖)
      (fun w _ => norm_nonneg _)
  calc
    orderedDerivativeFamilyNorm v j (fun _ : Unit => f) x =
        Real.sqrt (∑ w : Fin j → I, ‖iteratedFDeriv ℝ j f x (v ∘ w)‖ ^ 2) := by
      simp [orderedDerivativeFamilyNorm_eq_sqrt]
    _ ≤ Real.sqrt ((∑ w : Fin j → I, ‖iteratedFDeriv ℝ j f x (v ∘ w)‖) ^ 2) :=
      Real.sqrt_le_sqrt hsq
    _ = ∑ w : Fin j → I, ‖iteratedFDeriv ℝ j f x (v ∘ w)‖ :=
      Real.sqrt_sq (Finset.sum_nonneg fun w _ => norm_nonneg _)
    _ ≤ ∑ _w : Fin j → I, ‖iteratedFDeriv ℝ j f x‖ := by
      apply Finset.sum_le_sum
      intro w hw
      apply ContinuousMultilinearMap.unit_le_opNorm
      exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => hv (w i)
    _ = (Fintype.card I : ℝ) ^ j * ‖iteratedFDeriv ℝ j f x‖ := by
      simp

private theorem derivWordNorm_le_card_pow_opNorm {d : ℕ}
    (j : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℂ) (x : EuclideanSpace ℝ (Fin d)) :
    derivWordNorm j f x ≤ (d : ℝ) ^ j * ‖iteratedFDeriv ℝ j f x‖ := by
  simpa [orderedDerivativeFamilyNorm_eq_sqrt, derivWordNorm, Function.comp_def] using
    singletonTensorNorm_le_card_pow (EuclideanSpace.basisFun (Fin d) ℝ)
      (fun i => (norm_basisFun i).le) j f x

private theorem derivWordNorm_le_factorial_of_bounds {d : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → ℂ} {s : Set (EuclideanSpace ℝ (Fin d))}
    {C A : ℝ} (hf : HasFactorialDerivativeBoundsOn f s C A)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ s) (j : ℕ) :
    derivWordNorm j f x ≤ C * ((d : ℝ) * A) ^ j * (j.factorial : ℝ) := by
  calc
    derivWordNorm j f x ≤ (d : ℝ) ^ j * ‖iteratedFDeriv ℝ j f x‖ :=
      derivWordNorm_le_card_pow_opNorm j f x
    _ ≤ (d : ℝ) ^ j * (C * A ^ j * (j.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left (hf x hx j) (by positivity)
    _ = C * ((d : ℝ) * A) ^ j * (j.factorial : ℝ) := by
      rw [mul_pow]
      ring

/-- Compact containment supplies the finiteness needed before real absorption. -/
private theorem ballWeightedSeminorm_lt_top_of_continuousOn {d : ℕ}
    {G : EuclideanSpace ℝ (Fin d) → ℝ} {x₀ : EuclideanSpace ℝ (Fin d)}
    {R : ℝ} (hR : 0 ≤ R) (hG : ContinuousOn G (closedBall x₀ R)) (m : ℕ) :
    ballWeightedSeminorm G x₀ R m < ⊤ := by
  have : IsFiniteMeasure (volume.restrict (closedBall x₀ R)) :=
    isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
  obtain ⟨C, hC⟩ := (isCompact_closedBall x₀ R).exists_bound_of_continuousOn hG
  have hLp : MemLp G 2 (volume.restrict (closedBall x₀ R)) :=
    MemLp.of_bound (hG.aestronglyMeasurable measurableSet_closedBall) C
      ((ae_restrict_iff' measurableSet_closedBall).2 (ae_of_all _ hC))
  have hbound : ballWeightedSeminorm G x₀ R m ≤
      ENNReal.ofReal (R ^ m) * eLpNorm G 2 (volume.restrict (closedBall x₀ R)) := by
    unfold ballWeightedSeminorm
    refine iSup₂_le fun ρ hρ => ?_
    have hρ0 : 0 ≤ ρ := (div_nonneg hR (by norm_num : (0 : ℝ) ≤ 2)).trans hρ.1
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) ?_
    · exact pow_le_pow_left₀ (sub_nonneg.2 hρ.2.le) (sub_le_self R hρ0) m
    · exact eLpNorm_mono_measure G
        (Measure.restrict_mono ((ball_subset_ball hρ.2.le).trans ball_subset_closedBall) le_rfl)
  exact hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hLp.eLpNorm_lt_top)

private theorem ballWeightedSeminorm_derivWordNorm_lt_top {d : ℕ}
    {u : EuclideanSpace ℝ (Fin d) → ℂ} {S : Set (EuclideanSpace ℝ (Fin d))}
    (hu : ContDiffOn ℝ ∞ u S) (hS : IsOpen S)
    {x₀ : EuclideanSpace ℝ (Fin d)} {R : ℝ}
    (hR : 0 ≤ R) (hsub : closedBall x₀ R ⊆ S) (j m : ℕ) :
    ballWeightedSeminorm (derivWordNorm j u) x₀ R m < ⊤ :=
  ballWeightedSeminorm_lt_top_of_continuousOn hR
    ((continuousOn_derivWordNorm hu hS j).mono hsub) m

private theorem weightedNorm_mono_on {d : ℕ}
    {F G : EuclideanSpace ℝ (Fin d) → ℝ} {x₀ : EuclideanSpace ℝ (Fin d)}
    {R : ℝ} (hF : ContinuousOn F (ball x₀ R))
    (hFG : ∀ x ∈ ball x₀ R, ‖F x‖ ≤ G x) (m : ℕ) :
    ballWeightedSeminorm F x₀ R m ≤ ballWeightedSeminorm G x₀ R m := by
  unfold ballWeightedSeminorm
  refine iSup₂_le fun ρ hρ => le_iSup₂_of_le ρ hρ ?_
  apply mul_le_mul' le_rfl
  apply eLpNorm_mono_ae_real
    ((hF.mono (ball_subset_ball hρ.2.le)).aestronglyMeasurable measurableSet_ball)
  exact (ae_restrict_iff' measurableSet_ball).2
    (ae_of_all _ fun x hx => hFG x (ball_subset_ball hρ.2.le hx))

private theorem weightedNorm_add_le {d : ℕ}
    (F G : EuclideanSpace ℝ (Fin d) → ℝ) (x₀ : EuclideanSpace ℝ (Fin d))
    (R : ℝ) (m : ℕ) :
    ballWeightedSeminorm (fun x => F x + G x) x₀ R m ≤
      ballWeightedSeminorm F x₀ R m + ballWeightedSeminorm G x₀ R m := by
  unfold ballWeightedSeminorm
  refine iSup₂_le fun ρ hρ => ?_
  calc
    ENNReal.ofReal ((R - ρ) ^ m) *
        eLpNorm (fun x => F x + G x) 2 (volume.restrict (ball x₀ ρ)) ≤
        ENNReal.ofReal ((R - ρ) ^ m) *
          (eLpNorm F 2 (volume.restrict (ball x₀ ρ)) +
            eLpNorm G 2 (volume.restrict (ball x₀ ρ))) :=
      mul_le_mul' le_rfl (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2))
    _ ≤ _ := by
      rw [mul_add]
      exact add_le_add (le_iSup₂_of_le ρ hρ le_rfl) (le_iSup₂_of_le ρ hρ le_rfl)

private theorem weightedNorm_sum_le {d : ℕ} {I : Type*} (s : Finset I)
    (F : I → EuclideanSpace ℝ (Fin d) → ℝ) (x₀ : EuclideanSpace ℝ (Fin d))
    (R : ℝ) (m : ℕ) :
    ballWeightedSeminorm (fun x => ∑ i ∈ s, F i x) x₀ R m ≤
      ∑ i ∈ s, ballWeightedSeminorm (F i) x₀ R m := by
  unfold ballWeightedSeminorm
  refine iSup₂_le fun ρ hρ => ?_
  have hsum : eLpNorm (fun x => ∑ i ∈ s, F i x) 2 (volume.restrict (ball x₀ ρ)) ≤
      ∑ i ∈ s, eLpNorm (F i) 2 (volume.restrict (ball x₀ ρ)) := by
    have heq : (fun x => ∑ i ∈ s, F i x) = ∑ i ∈ s, F i := by
      funext x
      simp
    rw [heq]
    exact eLpNorm_sum_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  calc
    _ ≤ ENNReal.ofReal ((R - ρ) ^ m) *
        (∑ i ∈ s, eLpNorm (F i) 2 (volume.restrict (ball x₀ ρ))) :=
      mul_le_mul' le_rfl hsum
    _ ≤ _ := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i hi => le_iSup₂_of_le ρ hρ le_rfl

private theorem weightedNorm_const_mul_le {d : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (G : EuclideanSpace ℝ (Fin d) → ℝ) (x₀ : EuclideanSpace ℝ (Fin d))
    (R : ℝ) (m : ℕ) :
    ballWeightedSeminorm (fun x => c * G x) x₀ R m ≤
      ENNReal.ofReal c * ballWeightedSeminorm G x₀ R m := by
  unfold ballWeightedSeminorm
  refine iSup₂_le fun ρ hρ => ?_
  have hsmul :
      eLpNorm (fun x => c * G x) 2 (volume.restrict (ball x₀ ρ)) =
        ENNReal.ofReal c * eLpNorm G 2 (volume.restrict (ball x₀ ρ)) := by
    change eLpNorm (c • G) 2 (volume.restrict (ball x₀ ρ)) = _
    simpa only [Real.enorm_eq_ofReal_abs, abs_of_nonneg hc] using
      (eLpNorm_const_smul c G 2 (volume.restrict (ball x₀ ρ)))
  rw [hsmul, mul_left_comm]
  exact mul_le_mul' le_rfl (le_iSup₂_of_le ρ hρ le_rfl)

private theorem weightedNorm_raise_weight_le {d : ℕ}
    (G : EuclideanSpace ℝ (Fin d) → ℝ) (x₀ : EuclideanSpace ℝ (Fin d))
    {R : ℝ} (hR : 0 ≤ R) {n m : ℕ} (hnm : n ≤ m) :
    ballWeightedSeminorm G x₀ R m ≤
      ENNReal.ofReal (R ^ (m - n)) * ballWeightedSeminorm G x₀ R n := by
  unfold ballWeightedSeminorm
  refine iSup₂_le fun ρ hρ => ?_
  have hρ0 : 0 ≤ ρ := (div_nonneg hR (by norm_num : (0 : ℝ) ≤ 2)).trans hρ.1
  have ht : 0 ≤ R - ρ := sub_nonneg.2 hρ.2.le
  have hpow : (R - ρ) ^ m ≤ R ^ (m - n) * (R - ρ) ^ n := by
    rw [← Nat.sub_add_cancel hnm, pow_add, Nat.add_sub_cancel]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ ht (sub_le_self R hρ0) (m - n)) (pow_nonneg ht n)
  calc
    _ ≤ ENNReal.ofReal (R ^ (m - n) * (R - ρ) ^ n) *
        eLpNorm G 2 (volume.restrict (ball x₀ ρ)) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal hpow) le_rfl
    _ ≤ _ := by
      rw [ENNReal.ofReal_mul (pow_nonneg hR _), mul_assoc]
      exact mul_le_mul' le_rfl (le_iSup₂_of_le ρ hρ le_rfl)

private theorem canonical_singletonTensorNorm_eq {d : ℕ}
    (j : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℂ) (x : EuclideanSpace ℝ (Fin d)) :
    orderedDerivativeFamilyNorm (EuclideanSpace.basisFun (Fin d) ℝ) j
      (fun _ : Unit => f) x = derivWordNorm j f x := by
  simp [orderedDerivativeFamilyNorm_eq_sqrt, derivWordNorm, Function.comp_def]

private theorem derivWordNorm_eq_zero_of_eqOn_zero {d : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → ℂ} {S : Set (EuclideanSpace ℝ (Fin d))}
    (hS : IsOpen S) (hf : ∀ x ∈ S, f x = 0)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ S) (j : ℕ) :
    derivWordNorm j f x = 0 := by
  have heq : f =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) :=
    Filter.eventually_of_mem (hS.mem_nhds hx) hf
  rw [derivWordNorm_congr_of_eventuallyEq heq j]
  simp [derivWordNorm]

/-- Specialization of the sharp frozen bound to the actual canonical norm,
with uniform bounds on the coefficient tensors. -/
private theorem canonicalFrozen_pointwise_le {d r : ℕ}
    (D : CoordinateScalarOperator (EuclideanSpace ℝ (Fin d)) d r)
    (hD : D.basis = (EuclideanSpace.basisFun (Fin d) ℝ).toBasis)
    {S : Set (EuclideanSpace ℝ (Fin d))} (hS : IsOpen S)
    (hcoef : ∀ (k : Fin (r + 1)) (w : Fin k.val → Fin d),
      ContDiffOn ℝ ∞ (D.coefficient k w) S)
    {u : EuclideanSpace ℝ (Fin d) → ℂ} (hu : ContDiffOn ℝ ∞ u S)
    (heq : ∀ x ∈ S, D.action u x = 0)
    (b : ℕ → ℝ)
    (hb : ∀ (k : Fin (r + 1)) (w : Fin k.val → Fin d)
      (j : ℕ) (x), x ∈ S → derivWordNorm j (D.coefficient k w) x ≤ b j)
    (x₀ : EuclideanSpace ℝ (Fin d)) (ε : ℝ)
    (hvar : ∀ x ∈ S, (∑ w : Fin r → Fin d,
      ‖D.coefficient (Fin.last r) w x₀ - D.coefficient (Fin.last r) w x‖) ≤ ε)
    (p : ℕ) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ S) :
    derivWordNorm p (constCoeffAction (fun w => D.coefficient (Fin.last r) w x₀) u) x ≤
      ε * derivWordNorm (p + r) u x +
      (∑ _w : Fin r → Fin d, ∑ j ∈ Finset.range p,
        (p.choose (j + 1) : ℝ) * b (j + 1) * derivWordNorm (p - (j + 1) + r) u x) +
      ∑ k : Fin r, ∑ _w : Fin k.val → Fin d, ∑ j ∈ Finset.range (p + 1),
        (p.choose j : ℝ) * b j * derivWordNorm (p - j + k.val) u x := by
  have h := coordinateScalarFrozenDerivativeEstimate
    (E := EuclideanSpace ℝ (Fin d)) d r D S hS hcoef u hu x₀ p x hx
  have hv : (fun i => D.basis i) =
      (EuclideanSpace.basisFun (Fin d) ℝ : Fin d → EuclideanSpace ℝ (Fin d)) := by
    rw [hD]
    rfl
  have hz := derivWordNorm_eq_zero_of_eqOn_zero hS heq hx p
  have hbase :
      derivWordNorm p (constCoeffAction (fun w => D.coefficient (Fin.last r) w x₀) u) x ≤
      (∑ w : Fin r → Fin d,
        ‖D.coefficient (Fin.last r) w x₀ - D.coefficient (Fin.last r) w x‖) *
          derivWordNorm (p + r) u x +
      (∑ w : Fin r → Fin d, ∑ j ∈ Finset.range p,
        (p.choose (j + 1) : ℝ) * derivWordNorm (j + 1) (D.coefficient (Fin.last r) w) x *
          derivWordNorm (p - (j + 1) + r) u x) +
      ∑ k : Fin r, ∑ w : Fin k.val → Fin d, ∑ j ∈ Finset.range (p + 1),
        (p.choose j : ℝ) * derivWordNorm j (D.coefficient k.castSucc w) x *
          derivWordNorm (p - j + k.val) u x := by
    change derivWordNorm p (fun y => ∑ w : Fin r → Fin d,
      D.coefficient (Fin.last r) w x₀ *
        iteratedFDeriv ℝ r u y
          (fun i => EuclideanSpace.basisFun (Fin d) ℝ (w i))) x ≤ _
    simpa only [hv, canonical_singletonTensorNorm_eq, hz, zero_add,
      constCoeffAction, Function.comp_def] using h
  refine hbase.trans (add_le_add (add_le_add ?_ ?_) ?_)
  · exact mul_le_mul_of_nonneg_right (hvar x hx) (derivWordNorm_nonneg _ _ _)
  · apply Finset.sum_le_sum
    intro w hw
    apply Finset.sum_le_sum
    intro j hj
    apply mul_le_mul_of_nonneg_right ?_ (derivWordNorm_nonneg _ _ _)
    exact mul_le_mul_of_nonneg_left (hb (Fin.last r) w (j + 1) x hx) (by positivity)
  · apply Finset.sum_le_sum
    intro k hk
    apply Finset.sum_le_sum
    intro w hw
    apply Finset.sum_le_sum
    intro j hj
    apply mul_le_mul_of_nonneg_right ?_ (derivWordNorm_nonneg _ _ _)
    exact mul_le_mul_of_nonneg_left (hb k.castSucc w j x hx) (by positivity)

private theorem weightedNorm_const_mul_raise_le {d : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (G : EuclideanSpace ℝ (Fin d) → ℝ) (x₀ : EuclideanSpace ℝ (Fin d))
    {R : ℝ} (hR : 0 ≤ R) {n m : ℕ} (hnm : n ≤ m) :
    ballWeightedSeminorm (fun x => c * G x) x₀ R m ≤
      ENNReal.ofReal (c * R ^ (m - n)) * ballWeightedSeminorm G x₀ R n := by
  calc
    _ ≤ ENNReal.ofReal c * ballWeightedSeminorm G x₀ R m :=
      weightedNorm_const_mul_le hc G x₀ R m
    _ ≤ ENNReal.ofReal c *
        (ENNReal.ofReal (R ^ (m - n)) * ballWeightedSeminorm G x₀ R n) :=
      mul_le_mul' le_rfl (weightedNorm_raise_weight_le G x₀ hR hnm)
    _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul hc]

private theorem contDiffOn_constCoeffAction {d r : ℕ}
    {a : (Fin r → Fin d) → ℂ} {u : EuclideanSpace ℝ (Fin d) → ℂ}
    {S : Set (EuclideanSpace ℝ (Fin d))}
    (hu : ContDiffOn ℝ ∞ u S) (hS : IsOpen S) :
    ContDiffOn ℝ ∞ (constCoeffAction a u) S := by
  change ContDiffOn ℝ ∞ (fun x => ∑ w : Fin r → Fin d,
    a w • iteratedLineDeriv ℝ r u
      (fun i => EuclideanSpace.basisFun (Fin d) ℝ (w i)) x) S
  exact ContDiffOn.sum fun w _ =>
    (contDiffOn_infty_iteratedLineDeriv hu hS _).const_smul (a w)

/-- The actual differentiated equation, lifted to the weighted `L²` seminorm.
Each coefficient derivative costs its own missing weight, not a dimension
factor depending on the total derivative order of the solution. -/
private theorem canonicalFrozen_weighted_le {d r : ℕ}
    (D : CoordinateScalarOperator (EuclideanSpace ℝ (Fin d)) d r)
    (hD : D.basis = (EuclideanSpace.basisFun (Fin d) ℝ).toBasis)
    (x₀ : EuclideanSpace ℝ (Fin d)) {R : ℝ} (hR : 0 ≤ R)
    (hcoef : ∀ (k : Fin (r + 1)) (w : Fin k.val → Fin d),
      ContDiffOn ℝ ∞ (D.coefficient k w) (ball x₀ R))
    {u : EuclideanSpace ℝ (Fin d) → ℂ}
    (hu : ContDiffOn ℝ ∞ u (ball x₀ R))
    (heq : ∀ x ∈ ball x₀ R, D.action u x = 0)
    (b : ℕ → ℝ) (hb0 : ∀ j, 0 ≤ b j)
    (hb : ∀ (k : Fin (r + 1)) (w : Fin k.val → Fin d)
      (j : ℕ) (x), x ∈ ball x₀ R → derivWordNorm j (D.coefficient k w) x ≤ b j)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hvar : ∀ x ∈ ball x₀ R, (∑ w : Fin r → Fin d,
      ‖D.coefficient (Fin.last r) w x₀ - D.coefficient (Fin.last r) w x‖) ≤ ε)
    (p : ℕ) :
    ballWeightedSeminorm
      (derivWordNorm p (constCoeffAction (fun w => D.coefficient (Fin.last r) w x₀) u))
      x₀ R (p + r) ≤
      ENNReal.ofReal ε * ballWeightedSeminorm (derivWordNorm (p + r) u) x₀ R (p + r) +
      (∑ _w : Fin r → Fin d, ∑ j ∈ Finset.range p,
        ENNReal.ofReal ((p.choose (j + 1) : ℝ) * b (j + 1) * R ^ (j + 1)) *
          ballWeightedSeminorm (derivWordNorm (p - (j + 1) + r) u)
            x₀ R (p - (j + 1) + r)) +
      ∑ k : Fin r, ∑ _w : Fin k.val → Fin d, ∑ j ∈ Finset.range (p + 1),
        ENNReal.ofReal ((p.choose j : ℝ) * b j * R ^ (r - k.val + j)) *
          ballWeightedSeminorm (derivWordNorm (p - j + k.val) u)
            x₀ R (p - j + k.val) := by
  let T := fun x => ∑ _w : Fin r → Fin d, ∑ j ∈ Finset.range p,
    (p.choose (j + 1) : ℝ) * b (j + 1) * derivWordNorm (p - (j + 1) + r) u x
  let L := fun x => ∑ k : Fin r, ∑ _w : Fin k.val → Fin d, ∑ j ∈ Finset.range (p + 1),
    (p.choose j : ℝ) * b j * derivWordNorm (p - j + k.val) u x
  have hm := weightedNorm_mono_on
    (continuousOn_derivWordNorm (contDiffOn_constCoeffAction hu isOpen_ball) isOpen_ball p)
    (G := fun x => ε * derivWordNorm (p + r) u x + T x + L x)
    (fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (derivWordNorm_nonneg _ _ _)]
      exact canonicalFrozen_pointwise_le D hD isOpen_ball hcoef hu heq b hb x₀ ε hvar p hx)
    (p + r)
  refine hm.trans ((weightedNorm_add_le _ _ x₀ R (p + r)).trans (add_le_add
    ((weightedNorm_add_le _ _ x₀ R (p + r)).trans (add_le_add
      (weightedNorm_const_mul_le hε _ x₀ R (p + r)) ?_)) ?_))
  · refine (weightedNorm_sum_le Finset.univ _ x₀ R (p + r)).trans ?_
    apply Finset.sum_le_sum
    intro w hw
    refine (weightedNorm_sum_le (Finset.range p) _ x₀ R (p + r)).trans ?_
    apply Finset.sum_le_sum
    intro j hj
    have hjp : j + 1 ≤ p := Finset.mem_range.1 hj
    have he : p + r - (p - (j + 1) + r) = j + 1 := by omega
    simpa only [he] using weightedNorm_const_mul_raise_le
      (mul_nonneg (Nat.cast_nonneg _) (hb0 (j + 1)))
      (derivWordNorm (p - (j + 1) + r) u) x₀ hR (by omega : p - (j + 1) + r ≤ p + r)
  · refine (weightedNorm_sum_le Finset.univ _ x₀ R (p + r)).trans ?_
    apply Finset.sum_le_sum
    intro k hk
    refine (weightedNorm_sum_le Finset.univ _ x₀ R (p + r)).trans ?_
    apply Finset.sum_le_sum
    intro w hw
    refine (weightedNorm_sum_le (Finset.range (p + 1)) _ x₀ R (p + r)).trans ?_
    apply Finset.sum_le_sum
    intro j hj
    have hjp : j ≤ p := Nat.le_of_lt_succ (Finset.mem_range.1 hj)
    have he : p + r - (p - j + k.val) = r - k.val + j := by omega
    simpa only [he] using weightedNorm_const_mul_raise_le
      (mul_nonneg (Nat.cast_nonneg _) (hb0 j))
      (derivWordNorm (p - j + k.val) u) x₀ hR (by omega : p - j + k.val ≤ p + r)

private theorem choose_factorial_cancel {p j : ℕ} (hj : j ≤ p) :
    (1 / (p.factorial : ℝ)) * (p.choose j : ℝ) * (j.factorial : ℝ) =
      1 / ((p - j).factorial : ℝ) := by
  have hfac : (p.choose j : ℝ) * (j.factorial : ℝ) * ((p - j).factorial : ℝ) =
      (p.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj
  have hp : (p.factorial : ℝ) ≠ 0 := by positivity
  have hpj : ((p - j).factorial : ℝ) ≠ 0 := by positivity
  apply (mul_right_inj' hpj).1
  calc
    _ = (1 / (p.factorial : ℝ)) *
        ((p.choose j : ℝ) * (j.factorial : ℝ) * ((p - j).factorial : ℝ)) := by ring
    _ = 1 := by rw [hfac]; field_simp
    _ = _ := by field_simp

/-- Factorial normalisation for a lower operator coefficient. Truncated
subtraction also covers total derivative orders below the operator order. -/
private theorem lower_factorial_cancel_le {p j k r : ℕ}
    (hj : j ≤ p) (hk : k ≤ r) :
    (1 / (p.factorial : ℝ)) * (p.choose j : ℝ) * (j.factorial : ℝ) ≤
      1 / ((p - j + k - r).factorial : ℝ) := by
  rw [choose_factorial_cancel hj]
  apply one_div_le_one_div_of_le
  · positivity
  · exact_mod_cast Nat.factorial_le (by omega : p - j + k - r ≤ p - j)

private theorem canonicalFrozen_real_le {d r : ℕ}
    (D : CoordinateScalarOperator (EuclideanSpace ℝ (Fin d)) d r)
    (hD : D.basis = (EuclideanSpace.basisFun (Fin d) ℝ).toBasis)
    (x₀ : EuclideanSpace ℝ (Fin d)) {R : ℝ} (hR : 0 ≤ R)
    (hcoef : ∀ (k : Fin (r + 1)) (w : Fin k.val → Fin d),
      ContDiffOn ℝ ∞ (D.coefficient k w) (ball x₀ R))
    {u : EuclideanSpace ℝ (Fin d) → ℂ}
    (hu : ContDiffOn ℝ ∞ u (ball x₀ R))
    (heq : ∀ x ∈ ball x₀ R, D.action u x = 0)
    (b : ℕ → ℝ) (hb0 : ∀ j, 0 ≤ b j)
    (hb : ∀ (k : Fin (r + 1)) (w : Fin k.val → Fin d)
      (j : ℕ) (x), x ∈ ball x₀ R → derivWordNorm j (D.coefficient k w) x ≤ b j)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hvar : ∀ x ∈ ball x₀ R, (∑ w : Fin r → Fin d,
      ‖D.coefficient (Fin.last r) w x₀ - D.coefficient (Fin.last r) w x‖) ≤ ε)
    (hfin : ∀ k, ballWeightedSeminorm (derivWordNorm k u) x₀ R k ≠ ⊤)
    (p : ℕ) :
    let N := fun k => (ballWeightedSeminorm (derivWordNorm k u) x₀ R k).toReal
    (ballWeightedSeminorm
      (derivWordNorm p (constCoeffAction (fun w => D.coefficient (Fin.last r) w x₀) u))
      x₀ R (p + r)).toReal ≤
      ε * N (p + r) +
      (∑ _w : Fin r → Fin d, ∑ j ∈ Finset.range p,
        ((p.choose (j + 1) : ℝ) * b (j + 1) * R ^ (j + 1)) * N (p - (j + 1) + r)) +
      ∑ k : Fin r, ∑ _w : Fin k.val → Fin d, ∑ j ∈ Finset.range (p + 1),
        ((p.choose j : ℝ) * b j * R ^ (r - k.val + j)) * N (p - j + k.val) := by
  have h := canonicalFrozen_weighted_le D hD x₀ hR hcoef hu heq b hb0 hb hε hvar p
  have hprod (c : ℝ) (k : ℕ) :
      ENNReal.ofReal c * ballWeightedSeminorm (derivWordNorm k u) x₀ R k ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin k)
  have hconv (s : Finset ℕ) (c : ℕ → ℝ) (n : ℕ → ℕ) :
      (∑ i ∈ s, ENNReal.ofReal (c i) *
        ballWeightedSeminorm (derivWordNorm (n i) u) x₀ R (n i)).toReal =
      ∑ i ∈ s, (ENNReal.ofReal (c i)).toReal *
        (ballWeightedSeminorm (derivWordNorm (n i) u) x₀ R (n i)).toReal := by
    rw [ENNReal.toReal_sum (fun i _ => hprod (c i) (n i))]
    simp only [ENNReal.toReal_mul]
  have hT : (∑ _w : Fin r → Fin d, ∑ j ∈ Finset.range p,
      ENNReal.ofReal ((p.choose (j + 1) : ℝ) * b (j + 1) * R ^ (j + 1)) *
        ballWeightedSeminorm (derivWordNorm (p - (j + 1) + r) u)
          x₀ R (p - (j + 1) + r)) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun _ _ => ENNReal.sum_ne_top.2 fun _ _ => hprod _ _
  have hL : (∑ k : Fin r, ∑ _w : Fin k.val → Fin d, ∑ j ∈ Finset.range (p + 1),
      ENNReal.ofReal ((p.choose j : ℝ) * b j * R ^ (r - k.val + j)) *
        ballWeightedSeminorm (derivWordNorm (p - j + k.val) u)
          x₀ R (p - j + k.val)) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun _ _ => ENNReal.sum_ne_top.2 fun _ _ =>
      ENNReal.sum_ne_top.2 fun _ _ => hprod _ _
  have ht := ENNReal.toReal_mono
    (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hprod ε _, hT⟩, hL⟩) h
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hprod ε _, hT⟩) hL,
    ENNReal.toReal_add (hprod ε _) hT] at ht
  have hbR (a j : ℕ) : 0 ≤ (p.choose j : ℝ) * b j * R ^ a :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hb0 j)) (pow_nonneg hR _)
  simpa (disch := first | positivity | exact hbR _ _ |
    (simp only [ENNReal.sum_ne_top]; intros; exact hprod _ _)) only
    [hconv, ENNReal.toReal_sum, ENNReal.toReal_mul, ENNReal.toReal_ofReal] using ht

private theorem geometric_convolution_le {t A : ℝ} (ht : 0 ≤ t) (hA : 0 ≤ A)
    (htA : 2 * t ≤ A) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), t ^ j * A ^ (n - j)) ≤ 2 * A ^ n := by
  have hta : t ≤ A * (1 / 2) := by linarith
  calc
    (∑ j ∈ Finset.range (n + 1), t ^ j * A ^ (n - j)) ≤
        ∑ j ∈ Finset.range (n + 1), A ^ n * (1 / 2 : ℝ) ^ j := by
      apply Finset.sum_le_sum
      intro j hj
      have hjn : j ≤ n := by have := Finset.mem_range.1 hj; omega
      calc
        t ^ j * A ^ (n - j) ≤ (A * (1 / 2)) ^ j * A ^ (n - j) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht hta j) (pow_nonneg hA _)
        _ = (A ^ j * A ^ (n - j)) * (1 / 2 : ℝ) ^ j := by rw [mul_pow]; ring
        _ = _ := by rw [← pow_add, show j + (n - j) = n by omega]
    _ = A ^ n * (∑ j ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ j) := by
      rw [Finset.mul_sum]
    _ ≤ A ^ n * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le _) (pow_nonneg hA _)
    _ = _ := by ring

private theorem sequence_convolution_le (H : ℕ → ℝ) {C t A : ℝ}
    (hC : 0 ≤ C) (ht : 0 ≤ t) (hA : 0 ≤ A) (htA : 2 * t ≤ A)
    (p k : ℕ) (hH : ∀ j ≤ p, H (p - j + k) ≤ C * A ^ (p - j + k)) :
    (∑ j ∈ Finset.range (p + 1), t ^ j * H (p - j + k)) ≤ 2 * C * A ^ (p + k) := by
  calc
    (∑ j ∈ Finset.range (p + 1), t ^ j * H (p - j + k)) ≤
        ∑ j ∈ Finset.range (p + 1), C * A ^ k * (t ^ j * A ^ (p - j)) := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        t ^ j * H (p - j + k) ≤ t ^ j * (C * A ^ (p - j + k)) :=
          mul_le_mul_of_nonneg_left (hH j (by have := Finset.mem_range.1 hj; omega))
            (pow_nonneg ht _)
        _ = _ := by rw [pow_add]; ring
    _ = C * A ^ k * (∑ j ∈ Finset.range (p + 1), t ^ j * A ^ (p - j)) := by
      rw [Finset.mul_sum]
    _ ≤ C * A ^ k * (2 * A ^ p) :=
      mul_le_mul_of_nonneg_left (geometric_convolution_le ht hA htA p)
        (mul_nonneg hC (pow_nonneg hA _))
    _ = _ := by rw [pow_add]; ring

/-- A discrete majorant for the normalized elliptic recurrence. All recursive
indices are strictly smaller, even when natural subtraction is truncated. -/
private theorem exponential_bound_of_elliptic_recurrence
    {r : ℕ} (hr : 0 < r) (H : ℕ → ℝ) (hH0 : ∀ m, 0 ≤ H m)
    {B T t : ℝ} (hB : 0 ≤ B) (hT : 0 ≤ T) (ht : 0 ≤ t)
    (S : Fin r → ℝ) (hS : ∀ k, 0 ≤ S k)
    (hrec : ∀ p,
      H (r + p) ≤ B * (T *
        (∑ j ∈ Finset.range p, t ^ (j + 1) * H (p - (j + 1) + r)) +
        (∑ k : Fin r, S k *
          (∑ j ∈ Finset.range (p + 1), t ^ j * H (p - j + k.val))) +
        ∑ q ∈ Finset.Icc 1 r, H (r + p - q))) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ m, H m ≤ C * A ^ m := by
  classical
  let Q := 2 * T * t + 2 * ∑ k : Fin r, S k + (r : ℝ)
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    exact add_nonneg (add_nonneg (by positivity)
      (mul_nonneg (by norm_num) (Finset.sum_nonneg fun k _ => hS k))) (Nat.cast_nonneg _)
  let A := 1 + 2 * t + B * Q
  have hA1 : 1 ≤ A := by dsimp [A]; linarith [mul_nonneg hB hQ]
  have hAt : 2 * t ≤ A := by dsimp [A]; linarith [mul_nonneg hB hQ]
  have hAB : B * Q ≤ A := by dsimp [A]; linarith
  have hA : 0 < A := zero_lt_one.trans_le hA1
  let C := 1 + ∑ i ∈ Finset.range r, H i
  have hC : 0 < C := by
    dsimp [C]
    exact add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun i _ => hH0 i)
  refine ⟨C, A, hC, hA, fun m => ?_⟩
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hmr : m < r
    · have hb : H m ≤ C := by
        have hi := Finset.single_le_sum (fun i _ => hH0 i) (Finset.mem_range.2 hmr)
        dsimp [C]
        linarith
      exact hb.trans (le_mul_of_one_le_right hC.le (one_le_pow₀ hA1))
    · let p := m - r
      have hm : r + p = m := by dsimp [p]; omega
      have hm0 : 0 < m := by omega
      have htop :
          (∑ j ∈ Finset.range p, t ^ (j + 1) * H (p - (j + 1) + r)) ≤
            2 * t * C * A ^ (m - 1) := by
        cases hpdef : p with
        | zero => simp only [Finset.range_zero, Finset.sum_empty]; positivity
        | succ p =>
          have hp : ∀ j ≤ p, H (p - j + r) ≤ C * A ^ (p - j + r) :=
            fun j hj => ih _ (by omega)
          have hc := sequence_convolution_le H hC.le ht hA.le hAt p r hp
          calc
            (∑ j ∈ Finset.range (p + 1),
                t ^ (j + 1) * H (p + 1 - (j + 1) + r)) =
                t * ∑ j ∈ Finset.range (p + 1), t ^ j * H (p - j + r) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              rw [Nat.add_sub_add_right, pow_succ]
              ring
            _ ≤ t * (2 * C * A ^ (p + r)) := mul_le_mul_of_nonneg_left hc ht
            _ = _ := by rw [show p + r = m - 1 by omega]; ring
      have hlower (k : Fin r) :
          (∑ j ∈ Finset.range (p + 1), t ^ j * H (p - j + k.val)) ≤
            2 * C * A ^ (m - 1) := by
        have hp : ∀ j ≤ p, H (p - j + k.val) ≤ C * A ^ (p - j + k.val) :=
          fun j hj => ih _ (by have := k.isLt; omega)
        exact (sequence_convolution_le H hC.le ht hA.le hAt p k.val hp).trans
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hA1 (by have := k.isLt; omega : p + k.val ≤ m - 1))
            (by positivity))
      have hcut :
          (∑ q ∈ Finset.Icc 1 r, H (r + p - q)) ≤ (r : ℝ) * (C * A ^ (m - 1)) := by
        calc
          (∑ q ∈ Finset.Icc 1 r, H (r + p - q)) ≤
              ∑ _q ∈ Finset.Icc 1 r, C * A ^ (m - 1) := by
            apply Finset.sum_le_sum
            intro q hq
            have hq1 := (Finset.mem_Icc.1 hq).1
            exact (ih _ (by omega)).trans
              (mul_le_mul_of_nonneg_left
                (pow_le_pow_right₀ hA1 (by omega : r + p - q ≤ m - 1)) hC.le)
          _ = _ := by simp
      have htot :
          T * (∑ j ∈ Finset.range p, t ^ (j + 1) * H (p - (j + 1) + r)) +
            (∑ k : Fin r, S k * (∑ j ∈ Finset.range (p + 1), t ^ j * H (p - j + k.val))) +
            (∑ q ∈ Finset.Icc 1 r, H (r + p - q)) ≤ Q * (C * A ^ (m - 1)) := by
        calc
          _ ≤ T * (2 * t * C * A ^ (m - 1)) +
              (∑ k : Fin r, S k * (2 * C * A ^ (m - 1))) +
              (r : ℝ) * (C * A ^ (m - 1)) :=
            add_le_add (add_le_add (mul_le_mul_of_nonneg_left htop hT)
              (Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hlower k) (hS k))) hcut
          _ = _ := by rw [← Finset.sum_mul]; dsimp [Q]; ring
      calc
        H m ≤ B * (Q * (C * A ^ (m - 1))) := by
          simpa only [hm] using (hrec p).trans (mul_le_mul_of_nonneg_left htot hB)
        _ = B * Q * (C * A ^ (m - 1)) := by ring
        _ ≤ A * (C * A ^ (m - 1)) :=
          mul_le_mul_of_nonneg_right hAB (mul_nonneg hC.le (pow_nonneg hA.le _))
        _ = C * A ^ m := by
          calc
            _ = C * (A ^ (m - 1) * A) := by ring
            _ = _ := by rw [← pow_succ, show m - 1 + 1 = m by omega]

private theorem normalized_frozen_bound {d r p : ℕ}
    (N : ℕ → ℝ) (hN : ∀ m, 0 ≤ N m)
    {C L R ε M : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hM : M ≤ ε * N (p + r) +
      (∑ _w : Fin r → Fin d, ∑ j ∈ Finset.range p,
        ((p.choose (j + 1) : ℝ) * (C * L ^ (j + 1) * ((j + 1).factorial : ℝ)) *
          R ^ (j + 1)) * N (p - (j + 1) + r)) +
      ∑ k : Fin r, ∑ _w : Fin k.val → Fin d, ∑ j ∈ Finset.range (p + 1),
        ((p.choose j : ℝ) * (C * L ^ j * (j.factorial : ℝ)) *
          R ^ (r - k.val + j)) * N (p - j + k.val)) :
    let H := fun m => (1 / ((m - r).factorial : ℝ)) * N m
    (1 / (p.factorial : ℝ)) * M ≤
      ε * H (r + p) +
      C * (d : ℝ) ^ r *
        (∑ j ∈ Finset.range p, (L * R) ^ (j + 1) * H (p - (j + 1) + r)) +
      ∑ k : Fin r, (C * (d : ℝ) ^ k.val * R ^ (r - k.val)) *
        (∑ j ∈ Finset.range (p + 1), (L * R) ^ j * H (p - j + k.val)) := by
  classical
  let H := fun m => (1 / ((m - r).factorial : ℝ)) * N m
  have htop (j : ℕ) (hj : j ≤ p) :
      (1 / (p.factorial : ℝ)) *
        (((p.choose j : ℝ) * (C * L ^ j * (j.factorial : ℝ)) * R ^ j) *
          N (p - j + r)) =
        C * (L * R) ^ j * H (p - j + r) := by
    dsimp [H]
    rw [Nat.add_sub_cancel, mul_pow]
    calc
      _ = C * L ^ j * R ^ j *
          ((1 / (p.factorial : ℝ)) * (p.choose j : ℝ) * (j.factorial : ℝ)) *
          N (p - j + r) := by ring
      _ = _ := by rw [choose_factorial_cancel hj]; ring
  have hlower (k : Fin r) (j : ℕ) (hj : j ≤ p) :
      (1 / (p.factorial : ℝ)) *
        (((p.choose j : ℝ) * (C * L ^ j * (j.factorial : ℝ)) *
          R ^ (r - k.val + j)) * N (p - j + k.val)) ≤
        C * R ^ (r - k.val) * (L * R) ^ j * H (p - j + k.val) := by
    dsimp [H]
    rw [pow_add, mul_pow]
    calc
      _ = (C * R ^ (r - k.val) * (L ^ j * R ^ j) * N (p - j + k.val)) *
          ((1 / (p.factorial : ℝ)) * (p.choose j : ℝ) * (j.factorial : ℝ)) := by ring
      _ ≤ (C * R ^ (r - k.val) * (L ^ j * R ^ j) * N (p - j + k.val)) *
          (1 / ((p - j + k.val - r).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (lower_factorial_cancel_le hj (Nat.le_of_lt k.isLt))
          (by have hn := hN (p - j + k.val); positivity)
      _ = _ := by ring
  have ht :
      (1 / (p.factorial : ℝ)) *
        (∑ _w : Fin r → Fin d, ∑ j ∈ Finset.range p,
          ((p.choose (j + 1) : ℝ) * (C * L ^ (j + 1) * ((j + 1).factorial : ℝ)) *
            R ^ (j + 1)) * N (p - (j + 1) + r)) =
        C * (d : ℝ) ^ r *
          (∑ j ∈ Finset.range p, (L * R) ^ (j + 1) * H (p - (j + 1) + r)) := by
    simp_rw [Finset.mul_sum]
    have he : ∀ j ∈ Finset.range p,
        (1 / (p.factorial : ℝ)) *
          (((p.choose (j + 1) : ℝ) * (C * L ^ (j + 1) * ((j + 1).factorial : ℝ)) *
            R ^ (j + 1)) * N (p - (j + 1) + r)) =
          C * (L * R) ^ (j + 1) * H (p - (j + 1) + r) :=
      fun j hj => htop (j + 1) (Finset.mem_range.1 hj)
    simp_rw [Finset.sum_congr rfl he]
    have hs :
        (∑ j ∈ Finset.range p, C * (L * R) ^ (j + 1) * H (p - (j + 1) + r)) =
          C * (∑ j ∈ Finset.range p, (L * R) ^ (j + 1) * H (p - (j + 1) + r)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hs]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow]
    rw [← Finset.mul_sum]
    ring
  have hl :
      (1 / (p.factorial : ℝ)) *
        (∑ k : Fin r, ∑ _w : Fin k.val → Fin d, ∑ j ∈ Finset.range (p + 1),
          ((p.choose j : ℝ) * (C * L ^ j * (j.factorial : ℝ)) *
            R ^ (r - k.val + j)) * N (p - j + k.val)) ≤
        ∑ k : Fin r, (C * (d : ℝ) ^ k.val * R ^ (r - k.val)) *
          (∑ j ∈ Finset.range (p + 1), (L * R) ^ j * H (p - j + k.val)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    calc
      _ = ∑ _w : Fin k.val → Fin d, ∑ j ∈ Finset.range (p + 1),
          (1 / (p.factorial : ℝ)) *
            (((p.choose j : ℝ) * (C * L ^ j * (j.factorial : ℝ)) *
              R ^ (r - k.val + j)) * N (p - j + k.val)) := by
        simp_rw [Finset.mul_sum]
      _ ≤ ∑ _w : Fin k.val → Fin d, ∑ j ∈ Finset.range (p + 1),
          C * R ^ (r - k.val) * (L * R) ^ j * H (p - j + k.val) := by
        apply Finset.sum_le_sum
        intro w hw
        exact Finset.sum_le_sum fun j hj =>
          hlower k j (by have := Finset.mem_range.1 hj; omega)
      _ = _ := by
        have hs :
            (∑ j ∈ Finset.range (p + 1),
              C * R ^ (r - k.val) * (L * R) ^ j * H (p - j + k.val)) =
              (C * R ^ (r - k.val)) *
                (∑ j ∈ Finset.range (p + 1), (L * R) ^ j * H (p - j + k.val)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [hs]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_pow]
        ring
  calc
    (1 / (p.factorial : ℝ)) * M ≤
        (1 / (p.factorial : ℝ)) * (ε * N (p + r) +
          (∑ _w : Fin r → Fin d, ∑ j ∈ Finset.range p,
            ((p.choose (j + 1) : ℝ) * (C * L ^ (j + 1) * ((j + 1).factorial : ℝ)) *
              R ^ (j + 1)) * N (p - (j + 1) + r)) +
          ∑ k : Fin r, ∑ _w : Fin k.val → Fin d, ∑ j ∈ Finset.range (p + 1),
            ((p.choose j : ℝ) * (C * L ^ j * (j.factorial : ℝ)) *
              R ^ (r - k.val + j)) * N (p - j + k.val)) :=
      mul_le_mul_of_nonneg_left hM (by positivity)
    _ ≤ _ := by
      rw [mul_add, mul_add, ht]
      have he : (1 / (p.factorial : ℝ)) * (ε * N (p + r)) = ε * H (r + p) := by
        dsimp [H]
        rw [Nat.add_sub_cancel_left, Nat.add_comm r p]
        ring
      rw [he]
      exact add_le_add le_rfl hl

private theorem exists_factorial_weighted_real_recursion {d r : ℕ}
    (a : (Fin r → Fin d) → ℂ) (K : ℝ) :
    ∃ K₃ : ℝ, 0 < K₃ ∧
      ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ)
        (u : EuclideanSpace ℝ (Fin d) → ℂ),
        ContDiffOn ℝ ∞ u (ball x₀ R) → ConstCoeffL2Bound a K (ball x₀ R) →
        (∀ m, ballWeightedSeminorm (derivWordNorm m u) x₀ R m ≠ ⊤) →
        (∀ p, ballWeightedSeminorm (derivWordNorm p (constCoeffAction a u))
          x₀ R (r + p) ≠ ⊤) →
        ∀ p,
          let H := fun m => (1 / ((m - r).factorial : ℝ)) *
            (ballWeightedSeminorm (derivWordNorm m u) x₀ R m).toReal
          H (r + p) ≤ K₃ *
            ((1 / (p.factorial : ℝ)) *
              (ballWeightedSeminorm (derivWordNorm p (constCoeffAction a u))
                x₀ R (r + p)).toReal +
              ∑ q ∈ Finset.Icc 1 r, H (r + p - q)) := by
  obtain ⟨K₃, hK₃, hrec⟩ := exists_factorial_weighted_recursion a K
  refine ⟨K₃, hK₃, fun x₀ R u hu hP hN hM p => ?_⟩
  let H := fun m => (1 / ((m - r).factorial : ℝ)) *
    (ballWeightedSeminorm (derivWordNorm m u) x₀ R m).toReal
  have hterm (q : ℕ) :
      ENNReal.ofReal (1 / ((p - q).factorial : ℝ)) *
        ballWeightedSeminorm (derivWordNorm (r + p - q) u) x₀ R (r + p - q) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hN _)
  have hsum :
      (∑ q ∈ Finset.Icc 1 r, ENNReal.ofReal (1 / ((p - q).factorial : ℝ)) *
        ballWeightedSeminorm (derivWordNorm (r + p - q) u) x₀ R (r + p - q)) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun q _ => hterm q
  have hfirst :
      ENNReal.ofReal (1 / (p.factorial : ℝ)) *
        ballWeightedSeminorm (derivWordNorm p (constCoeffAction a u)) x₀ R (r + p) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hM _)
  have hconv :
      (∑ q ∈ Finset.Icc 1 r, ENNReal.ofReal (1 / ((p - q).factorial : ℝ)) *
        ballWeightedSeminorm (derivWordNorm (r + p - q) u) x₀ R (r + p - q)).toReal =
        ∑ q ∈ Finset.Icc 1 r, H (r + p - q) := by
    rw [ENNReal.toReal_sum (fun q _ => hterm q)]
    apply Finset.sum_congr rfl
    intro q hq
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    dsimp [H]
    rw [show r + p - q - r = p - q by omega]
  have ht := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2 ⟨hfirst, hsum⟩))
    (hrec x₀ R u hu hP p)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hK₃.le,
    ENNReal.toReal_add hfirst hsum, hconv,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at ht
  simpa only [H, Nat.add_sub_cancel_left] using ht

private theorem absorb_half {K x Y : ℝ} (hK : 0 < K)
    (h : x ≤ K * ((1 / (2 * K)) * x + Y)) :
    x ≤ 2 * K * Y := by
  have he : K * (1 / (2 * K)) = (1 / 2 : ℝ) := by
    field_simp
  have hx : x ≤ (1 / 2 : ℝ) * x + K * Y := by
    calc
      x ≤ K * ((1 / (2 * K)) * x + Y) := h
      _ = _ := by rw [mul_add, ← mul_assoc, he]
  linarith

private theorem exponential_bound_of_frozen_recursion {r : ℕ} (hr : 0 < r)
    (H M : ℕ → ℝ) (hH : ∀ m, 0 ≤ H m)
    {K T t : ℝ} (hK : 0 < K) (hT : 0 ≤ T) (ht : 0 ≤ t)
    (S : Fin r → ℝ) (hS : ∀ k, 0 ≤ S k)
    (hrec : ∀ p, H (r + p) ≤ K *
      ((1 / (p.factorial : ℝ)) * M p + ∑ q ∈ Finset.Icc 1 r, H (r + p - q)))
    (hfrozen : ∀ p, (1 / (p.factorial : ℝ)) * M p ≤
      (1 / (2 * K)) * H (r + p) +
      T * (∑ j ∈ Finset.range p, t ^ (j + 1) * H (p - (j + 1) + r)) +
      ∑ k : Fin r, S k * (∑ j ∈ Finset.range (p + 1), t ^ j * H (p - j + k.val))) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ m, H m ≤ C * A ^ m := by
  apply exponential_bound_of_elliptic_recurrence (B := 2 * K) hr H hH
    (by positivity) hT ht S hS
  intro p
  apply absorb_half hK
  have h := (hrec p).trans (mul_le_mul_of_nonneg_left
    (add_le_add (hfrozen p) le_rfl) hK.le)
  simpa only [add_assoc] using h

private theorem factorial_bound_of_normalized_exponential_bound
    {r : ℕ} (N : ℕ → ℝ) {C A : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A)
    (h : ∀ m, (1 / ((m - r).factorial : ℝ)) * N m ≤ C * A ^ m) :
    ∀ m, N m ≤ C * A ^ m * (m.factorial : ℝ) := by
  intro m
  have hm : (0 : ℝ) < (m - r).factorial := by positivity
  calc
    N m = ((1 / ((m - r).factorial : ℝ)) * N m) *
        ((m - r).factorial : ℝ) := by field_simp
    _ ≤ C * A ^ m * ((m - r).factorial : ℝ) :=
      mul_le_mul_of_nonneg_right (h m) hm.le
    _ ≤ C * A ^ m * (m.factorial : ℝ) :=
      mul_le_mul_of_nonneg_left
        (by exact_mod_cast Nat.factorial_le (Nat.sub_le m r)) (by positivity)

private theorem exists_radius_independent_weighted_factorial_bound {d r : ℕ}
    (hr : 0 < r) (D : CoordinateScalarOperator (EuclideanSpace ℝ (Fin d)) d r)
    (hD : D.basis = (EuclideanSpace.basisFun (Fin d) ℝ).toBasis)
    (x₀ : EuclideanSpace ℝ (Fin d)) (K : ℝ) :
    ∃ K₃ : ℝ, 0 < K₃ ∧
      ∀ (S : Set (EuclideanSpace ℝ (Fin d))) (_hS : IsOpen S)
        (u : EuclideanSpace ℝ (Fin d) → ℂ),
        ContDiffOn ℝ ∞ u S →
        (∀ (k : Fin (r + 1)) (w : Fin k.val → Fin d),
          ContDiffOn ℝ ∞ (D.coefficient k w) S) →
        (∀ x ∈ S, D.action u x = 0) →
        ∀ R : ℝ, 0 ≤ R → closedBall x₀ R ⊆ S →
          ConstCoeffL2Bound (fun w => D.coefficient (Fin.last r) w x₀) K (ball x₀ R) →
          ∀ C L : ℝ, 0 ≤ C → 0 ≤ L →
            (∀ (k : Fin (r + 1)) (w : Fin k.val → Fin d)
              (j : ℕ) (x), x ∈ ball x₀ R →
                derivWordNorm j (D.coefficient k w) x ≤ C * L ^ j * (j.factorial : ℝ)) →
            (∀ x ∈ ball x₀ R, (∑ w : Fin r → Fin d,
              ‖D.coefficient (Fin.last r) w x₀ - D.coefficient (Fin.last r) w x‖) ≤
                1 / (2 * K₃)) →
            ∃ C₀ A₀ : ℝ, 0 < C₀ ∧ 0 < A₀ ∧
              ∀ m, ballWeightedSeminorm (derivWordNorm m u) x₀ R m ≤
                ENNReal.ofReal (C₀ * A₀ ^ m * (m.factorial : ℝ)) := by
  obtain ⟨K₃, hK₃, hrec⟩ := exists_factorial_weighted_real_recursion
    (fun w => D.coefficient (Fin.last r) w x₀) K
  refine ⟨K₃, hK₃, fun S hS u hu hcoef heq R hR hsub hP C L hC hL hb hvar => ?_⟩
  have hball : ball x₀ R ⊆ S := ball_subset_closedBall.trans hsub
  have hfin (m : ℕ) : ballWeightedSeminorm (derivWordNorm m u) x₀ R m ≠ ⊤ :=
    (ballWeightedSeminorm_derivWordNorm_lt_top hu hS hR hsub m m).ne
  have hMfin (p : ℕ) :
      ballWeightedSeminorm
        (derivWordNorm p (constCoeffAction (fun w => D.coefficient (Fin.last r) w x₀) u))
        x₀ R (r + p) ≠ ⊤ :=
    (ballWeightedSeminorm_derivWordNorm_lt_top (contDiffOn_constCoeffAction hu hS)
      hS hR hsub p (r + p)).ne
  let N := fun m => (ballWeightedSeminorm (derivWordNorm m u) x₀ R m).toReal
  let M := fun p => (ballWeightedSeminorm
    (derivWordNorm p (constCoeffAction (fun w => D.coefficient (Fin.last r) w x₀) u))
    x₀ R (r + p)).toReal
  let H := fun m => (1 / ((m - r).factorial : ℝ)) * N m
  have hH : ∀ m, 0 ≤ H m := fun m =>
    mul_nonneg (by positivity) ENNReal.toReal_nonneg
  have hnorm (p : ℕ) :
      (1 / (p.factorial : ℝ)) * M p ≤
        (1 / (2 * K₃)) * H (r + p) +
        C * (d : ℝ) ^ r *
          (∑ j ∈ Finset.range p, (L * R) ^ (j + 1) * H (p - (j + 1) + r)) +
        ∑ k : Fin r, (C * (d : ℝ) ^ k.val * R ^ (r - k.val)) *
          (∑ j ∈ Finset.range (p + 1), (L * R) ^ j * H (p - j + k.val)) := by
    have hfrozen := canonicalFrozen_real_le D hD x₀ hR
      (fun k w => (hcoef k w).mono hball) (hu.mono hball)
      (fun x hx => heq x (hball hx))
      (fun j => C * L ^ j * (j.factorial : ℝ)) (fun j => by positivity) hb
      (by positivity : 0 ≤ 1 / (2 * K₃)) hvar hfin p
    have hnorm := normalized_frozen_bound (d := d) (r := r) N
      (fun _ => ENNReal.toReal_nonneg) hC hL hR hfrozen
    simpa only [M, Nat.add_comm p r] using hnorm
  obtain ⟨C₀, A₀, hC₀, hA₀, hbound⟩ := exponential_bound_of_frozen_recursion hr H M hH
    hK₃ (by positivity : 0 ≤ C * (d : ℝ) ^ r) (mul_nonneg hL hR)
    (fun k : Fin r => C * (d : ℝ) ^ k.val * R ^ (r - k.val))
    (fun k => by positivity) (hrec x₀ R u (hu.mono hball) hP hfin hMfin) hnorm
  have hNbound := factorial_bound_of_normalized_exponential_bound N hC₀.le hA₀.le hbound
  refine ⟨C₀, A₀, hC₀, hA₀, fun m => ?_⟩
  exact (ENNReal.le_ofReal_iff_toReal_le (hfin m) (by positivity)).2 (hNbound m)

/-- Actual analytic coefficients and ellipticity give one shrinkable ball with
common factorial bounds for every ordered derivative tensor of the solution. -/
theorem canonicalScalarWeightedFactorialBounds {d r : ℕ} :
    CanonicalScalarWeightedFactorialBoundsStatement d r := by
  classical
  intro _hd hr D hD S hS hcoeff hell u hu heq x₀ hx₀ R₀ hR₀
  obtain ⟨U, _hU, hxU, c, hc, hsymbol⟩ :=
    coordinateScalarLocalEllipticity hr D x₀
      (fun w => (hcoeff (Fin.last r) w x₀ hx₀).continuousAt) (hell x₀ hx₀)
  have hfreq (ξ : EuclideanSpace ℝ (Fin d)) :
      c * ‖ξ‖ ^ r ≤ ‖∑ w : Fin r → Fin d,
        D.coefficient (Fin.last r) w x₀ * ∏ j : Fin r, (ξ (w j) : ℂ)‖ := by
    simpa only [innerSL_apply_norm, CoordinateScalarOperator.principalSymbol,
      hD, OrthonormalBasis.coe_toBasis, coe_innerSL_apply,
      EuclideanSpace.inner_basisFun_real] using hsymbol x₀ hxU (innerSL ℝ ξ)
  obtain ⟨K₃, hK₃, hfactorial⟩ :=
    exists_radius_independent_weighted_factorial_bound hr D hD x₀ c⁻¹
  obtain ⟨R₁, hR₁, hR₁le, C, hC, A, hA, hcoeffBounds⟩ :=
    hcoeff.exists_ball_hasFactorialDerivativeBoundsOn hx₀ hR₀
  have hvarContinuous :
      ContinuousAt (fun x => ∑ w : Fin r → Fin d,
        ‖D.coefficient (Fin.last r) w x₀ - D.coefficient (Fin.last r) w x‖) x₀ := by
    apply tendsto_finsetSum
    intro w _
    exact (continuousAt_const.sub
      (hcoeff (Fin.last r) w x₀ hx₀).continuousAt).norm
  have hε : (0 : ℝ) < 1 / (2 * K₃) := by positivity
  have hvarNear :
      ∀ᶠ x in 𝓝 x₀, (∑ w : Fin r → Fin d,
        ‖D.coefficient (Fin.last r) w x₀ - D.coefficient (Fin.last r) w x‖) <
          1 / (2 * K₃) := by
    apply hvarContinuous.eventually (p := fun y : ℝ => y < 1 / (2 * K₃))
    apply gt_mem_nhds
    simpa using hε
  have hSne : ∀ᶠ x in 𝓝 x₀, x ∈ S := hS.mem_nhds hx₀
  obtain ⟨δ, hδ, hδsub⟩ := Metric.eventually_nhds_iff_ball.1 (hSne.and hvarNear)
  let R := min R₁ δ / 2
  have hR : 0 < R := half_pos (lt_min hR₁ hδ)
  have hRsmall : R < min R₁ δ := half_lt_self (lt_min hR₁ hδ)
  have hR₁small : R < R₁ := hRsmall.trans_le (min_le_left _ _)
  have hδsmall : R < δ := hRsmall.trans_le (min_le_right _ _)
  have hclosed : closedBall x₀ R ⊆ S := fun x hx =>
    (hδsub x (closedBall_subset_ball hδsmall hx)).1
  have hball : ball x₀ R ⊆ ball x₀ R₁ := ball_subset_ball hR₁small.le
  obtain ⟨C₀, A₀, hC₀, hA₀, hbound⟩ := hfactorial S hS u hu
    (fun k w => (hcoeff k w).contDiffOn hS.uniqueDiffOn) heq R hR.le hclosed
    (constCoeffL2Bound_of_statement constantCoefficientEllipticL2Estimate hc hfreq _)
    C ((d : ℝ) * A) hC.le (by positivity)
    (fun k w j x hx =>
      derivWordNorm_le_factorial_of_bounds (hcoeffBounds k w).2 (hball hx) j)
    (fun x hx => (hδsub x
      (ball_subset_ball hδsmall.le hx)).2.le)
  exact ⟨R, C₀, A₀, hR, hR₁small.le.trans hR₁le, hclosed, hC₀, hA₀, hbound⟩

end Langlands.Analysis
