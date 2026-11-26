import Langlands.Representation.Archimedean.SmoothCasselmanWallachBound
import Langlands.Representation.Archimedean.OrthogonalGroupAveraging

/-! # Word estimates for lifts along open smooth quotient maps -/

noncomputable section

open MeasureTheory Set Langlands.CompactRepresentativeWeights
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open DerivativeSmoothVectors

universe uE uF

variable {n : ℕ}

local notation "I" n:max => matrixModel ℝ n
local notation "K" n:max => Matrix.unitaryGroup (Fin n) ℝ
local notation "G" n:max => Langlands.GeneralLinear n ℝ
local notation "M" n:max => Matrix (Fin n) (Fin n) ℝ
local notation "D[" n "," R "]" => DerivativeSmoothVectors (I n) R
local notation "F[" n "," R "]" => smoothKFinite ℝ n R

section CompactDensity

open OrthogonalFinitePolynomial

private theorem polynomial_le_finiteWeights :
    polynomialStar n ≤ (finiteWeights : StarSubalgebra ℂ C(K n, ℂ)) := by
  apply StarAlgebra.adjoin_le_iff.mpr
  rintro _ ⟨ij, rfl⟩
  change FiniteVectors.IsFiniteVector leftRegular (entry n ij)
  let P := Submodule.span ℂ (range (entry n))
  have : FiniteDimensional ℂ P := FiniteDimensional.span_of_finite ℂ (Set.finite_range (entry n))
  apply Submodule.finiteDimensional_of_le (S₂ := P)
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  have h : leftRegular k (entry n ij) =
      ∑ i : Fin n, ((k⁻¹ : K n).val ij.1 i : ℂ) • entry n (i, ij.2) := by
    apply ContinuousMap.ext
    intro x
    simp only [leftRegular_apply, entry_apply, Matrix.UnitaryGroup.mul_val,
      Matrix.mul_apply, Complex.ofReal_sum, Complex.ofReal_mul,
      ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  change leftRegular k (entry n ij) ∈ P
  rw [h]
  exact P.sum_mem fun i _ => P.smul_mem _ (Submodule.subset_span (mem_range_self (i, ij.2)))

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (R : G n →* (E →L[ℂ] E)) (hR : IsContinuousRepresentation R)
  (U : Submodule ℂ D[n,R]) (hU : IsClosed (U : Set D[n,R]))
  (hKU : ∀ (k : K n) (v : D[n,R]), v ∈ U → representation (I n) R (Unitary.toUnits k) v ∈ U)

local notation "ι" n:max => (ContinuousMap.mk Unitary.toUnits continuous_unitary_toUnits : C(K n, G n))
local notation "μ" n:max => (Measure.haar : Measure (K n))

include hR hKU hU in
set_option maxHeartbeats 600000 in
/-- A closed subspace of the genuine smooth carrier that is invariant under the orthogonal
action has a dense compact-finite part in the genuine derivative topology. -/
theorem le_topologicalClosure_smoothKFinite_inf : U ≤ (F[n,R] ⊓ U).topologicalClosure := by
  intro v hv
  let S := (F[n,R] ⊓ U).topologicalClosure
  change v ∈ S
  by_contra hnot
  obtain ⟨L, hLS, hvL⟩ := exists_functional_vanishing_on_closedSubmodule
    ((F[n,R] ⊓ U).isClosed_topologicalClosure) hnot
  let f : C(K n, ℂ) :=
    ⟨fun k => L (representation (I n) R (Unitary.toUnits k) v),
      L.continuous.comp ((continuous_representation_units R hR).comp
        (continuous_unitary_toUnits.prodMk continuous_const))⟩
  have htest : ∀ w ∈ polynomialStar n, ∫ k, w k * f k ∂(μ n) = 0 := by
    intro w hw
    let a := orthogonalSmoothAverage R hR (μ n) v w
    have hA (L' : D[n,R] →L[ℂ] ℂ) :
        L' a = ∫ k : K n, w k • L' (representation (I n) R (Unitary.toUnits k) v) ∂(μ n) :=
      apply_compactSmoothAverage R hR (μ n) (ι n) w v L'
    have haU : a ∈ U := by
      by_contra h
      obtain ⟨L', hL', ha'⟩ := exists_functional_vanishing_on_closedSubmodule hU h
      apply ha'
      rw [hA]
      apply integral_eq_zero_of_ae (Filter.Eventually.of_forall fun k => ?_)
      change w k • L' (representation (I n) R (Unitary.toUnits k) v) = (0 : ℂ)
      rw [hL' _ (hKU k v hv), smul_zero]
    have haF : a ∈ F[n,R] :=
      orthogonalSmoothAverage_mem_smoothKFinite R hR (μ n) v (polynomial_le_finiteWeights hw)
    have h := hLS a ((F[n,R] ⊓ U).le_topologicalClosure ⟨haF, haU⟩)
    rw [hA] at h
    exact h
  have h := congrArg (fun z : C(K n, ℂ) => z 1) (eq_zero_of_integral_polynomial_mul_eq_zero (μ n) f htest)
  apply hvL
  simpa only [f, ContinuousMap.coe_mk, map_one, Module.End.one_apply, ContinuousMap.zero_apply] using h

end CompactDensity

section Lifting

variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  (R : G n →* (E →L[ℂ] E)) (S : G n →* (F →L[ℂ] F))

local notation "p[" n "," R "]" => wordSeminormFamily (I n) R

/-- A continuous open smooth map that intertwines the compact actions and lifts each of
its compact-finite target vectors algebraically admits finite-word control on such lifts. -/
def RealSmoothQuotientWordLiftStatement [CompleteSpace E] : Prop :=
  ∀ Q : D[n,R] →L[ℂ] D[n,S],
    IsContinuousRepresentation R → IsOpenMap Q →
    (∀ (k : K n) (x : D[n,R]), Q (representation (I n) R (Unitary.toUnits k) x) =
      representation (I n) S (Unitary.toUnits k) (Q x)) →
    (∀ y ∈ F[n,S], ∃ x ∈ F[n,R], Q x = y) →
    ∀ J : Finset (List (M n)), ∃ (T : Finset (List (M n))) (C : ℝ), 0 ≤ C ∧
      ∀ y ∈ F[n,S], ∃ x ∈ F[n,R], Q x = y ∧
        (∑ Xs ∈ J, ‖derivativeCLM (I n) R Xs x‖) ≤ C * ∑ Ys ∈ T, ‖derivativeCLM (I n) S Ys y‖

private theorem exists_compactFinite_mem_open_of_mem_image
    (Q : D[n,R] →L[ℂ] D[n,S])
    (hker : Q.toLinearMap.ker ≤ (F[n,R] ⊓ Q.toLinearMap.ker).topologicalClosure)
    {U : Set D[n,R]} (hU : IsOpen U) {y : D[n,S]} (hy : y ∈ Q '' U)
    {z : D[n,R]} (hz : z ∈ F[n,R]) (hQz : Q z = y) :
    ∃ x ∈ F[n,R], x ∈ U ∧ Q x = y := by
  obtain ⟨w, hw, hQw⟩ := hy
  have hdiff : w - z ∈ Q.toLinearMap.ker := by
    change Q (w - z) = 0
    rw [map_sub, hQw, hQz, sub_self]
  have hV : IsOpen ((fun x : D[n,R] => x + z) ⁻¹' U) :=
    hU.preimage (continuous_id.add continuous_const)
  have hwz : w - z ∈ ((fun x : D[n,R] => x + z) ⁻¹' U) := by
    simpa only [mem_preimage, sub_add_cancel] using hw
  obtain ⟨d, hdV, hd⟩ := mem_closure_iff_nhds.mp (hker hdiff) _ (hV.mem_nhds hwz)
  have hQd : Q d = 0 := hd.2
  exact ⟨d + z, (F[n,R]).add_mem hd.1 hz, hdV, by rw [map_add, hQd, zero_add, hQz]⟩

/-- Openness and compact approximation inside the kernel give a controlled a priori
choice of algebraic lifts. -/
theorem realSmoothQuotientWordLift [CompleteSpace E] :
    RealSmoothQuotientWordLiftStatement R S := by
  classical
  intro Q hR hQ hK hsurj J
  let p : Seminorm ℂ D[n,R] := ∑ Xs ∈ J, p[n,R] Xs
  let U := {x : D[n,R] | p x < 1}
  have hp (x : D[n,R]) : p x = ∑ Xs ∈ J, ‖derivativeCLM (I n) R Xs x‖ := by
    simp only [p, FunLike.coe_sum, Finset.sum_apply, wordSeminormFamily_apply, derivativeCLM_apply]
  have hpc : Continuous p := by
    change Continuous (fun x : D[n,R] => p x)
    simp_rw [hp]
    exact continuous_finsetSum J fun Xs _ => (derivativeCLM (I n) R Xs).continuous.norm
  have hU : IsOpen U := isOpen_lt hpc continuous_const
  have h0 : (0 : D[n,S]) ∈ Q '' U := ⟨0, by simp [U], map_zero Q⟩
  obtain ⟨⟨T₀, ε⟩, hε, hT₀⟩ :=
    (withSeminorms_wordSeminormFamily (I n) S).hasBasis_zero_ball.mem_iff.mp
      ((hQ _ hU).mem_nhds h0)
  let T := insert [] T₀
  let q : Seminorm ℂ D[n,S] := ∑ Ys ∈ T, p[n,S] Ys
  have hq (y : D[n,S]) : q y = ∑ Ys ∈ T, ‖derivativeCLM (I n) S Ys y‖ := by
    simp only [q, FunLike.coe_sum, Finset.sum_apply, wordSeminormFamily_apply, derivativeCLM_apply]
  have hq_le (y : D[n,S]) : (T₀.sup p[n,S]) y ≤ q y := by
    apply Seminorm.finset_sup_apply_le (apply_nonneg q y)
    intro Ys hYs
    rw [hq, wordSeminormFamily_apply, ← derivativeCLM_apply]
    exact Finset.single_le_sum (fun Xs _ => norm_nonneg (derivativeCLM (I n) S Xs y))
      (Finset.mem_insert_of_mem hYs)
  have hker : Q.toLinearMap.ker ≤ (F[n,R] ⊓ Q.toLinearMap.ker).topologicalClosure :=
    le_topologicalClosure_smoothKFinite_inf R hR _ Q.isClosed_ker (fun k v hv => by
      change Q (representation (I n) R (Unitary.toUnits k) v) = 0
      rw [hK, show Q v = 0 from hv, map_zero])
  refine ⟨T, 2 / ε, by positivity, fun y hy => ?_⟩
  by_cases hy₀ : y = 0
  · subst y
    exact ⟨0, (F[n,R]).zero_mem, map_zero Q, by
      simp only [map_zero, norm_zero, Finset.sum_const_zero, mul_zero, le_refl]⟩
  have hqpos : 0 < q y := by
    have hle : ‖derivativeCLM (I n) S [] y‖ ≤ q y := by
      rw [hq]
      exact Finset.single_le_sum (fun Xs _ => norm_nonneg (derivativeCLM (I n) S Xs y))
        (Finset.mem_insert_self _ _)
    have hy' : derivativeCLM (I n) S [] y ≠ 0 := by
      intro h
      apply hy₀
      apply (toSmooth (I n) S).injective
      apply Subtype.ext
      simpa only [derivativeCLM_apply, iteratedLieDerivative_nil, map_zero, ZeroMemClass.coe_zero]
        using h
    exact (norm_pos_iff.mpr hy').trans_le hle
  let c : ℝ := ε / (2 * q y)
  have hc : 0 < c := by positivity
  let a : ℂ := c
  have ha : a ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hy' : a • y ∈ Q '' U := by
    apply hT₀
    rw [Seminorm.mem_ball_zero]
    refine (hq_le (a • y)).trans_lt ?_
    rw [map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg hc.le]
    have hcq : c * q y = ε / 2 := by
      dsimp only [c]
      field_simp
    linarith
  obtain ⟨z, hz, hQz⟩ := hsurj (a • y) ((F[n,S]).smul_mem _ hy)
  obtain ⟨x, hxF, hxU, hxQ⟩ := exists_compactFinite_mem_open_of_mem_image R S Q hker hU hy' hz hQz
  refine ⟨a⁻¹ • x, (F[n,R]).smul_mem _ hxF, ?_, ?_⟩
  · rw [map_smul, hxQ, inv_smul_smul₀ ha]
  · rw [← hp, ← hq, map_smul_eq_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hc.le]
    have hcInv : c⁻¹ = 2 / ε * q y := by
      dsimp only [c]
      field_simp
    have hpx : p x < 1 := hxU
    calc
      _ ≤ c⁻¹ * 1 := mul_le_mul_of_nonneg_left hpx.le (inv_nonneg.mpr hc.le)
      _ = _ := by rw [mul_one, hcInv]

end Lifting

end Langlands.Archimedean
