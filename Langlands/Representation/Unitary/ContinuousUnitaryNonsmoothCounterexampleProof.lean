import Langlands.Representation.Unitary.ContinuousUnitaryNonsmoothCounterexampleStatement
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Ring.Int
import Mathlib.Analysis.SpecificLimits.Normed

/-! # The continuous diagonal action of the product of sign groups -/

noncomputable section

open Filter Topology
open scoped ENNReal

namespace Langlands.Renard.CompactRepresentation

private abbrev Signs := ℕ → ℤˣ
private abbrev SquareSummable := lp (fun _ : ℕ => ℂ) 2

private def sign (u : ℤˣ) : ℂ := (u : ℤ)

private theorem norm_sign (u : ℤˣ) : ‖sign u‖ = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp [sign]

private def diagonal (g : Signs) : SquareSummable →ₗ[ℂ] SquareSummable where
  toFun v := ⟨fun n => sign (g n) * v n, (lp.memℓp v).mono' (fun n => by
    rw [norm_mul, norm_sign, one_mul])⟩
  map_add' v w := lp.ext (funext fun n => by
    change sign (g n) * (v n + w n) = sign (g n) * v n + sign (g n) * w n
    rw [mul_add])
  map_smul' c v := lp.ext (funext fun n => by
    change sign (g n) * (c * v n) = c * (sign (g n) * v n)
    rw [mul_left_comm])

private def signRepresentation : Representation ℂ Signs SquareSummable where
  toFun := diagonal
  map_one' := LinearMap.ext fun v => lp.ext (funext fun n => by
    change sign 1 * v n = v n
    simp [sign])
  map_mul' g h := LinearMap.ext fun v => lp.ext (funext fun n => by
    change sign (g n * h n) * v n = sign (g n) * (sign (h n) * v n)
    simp [sign, mul_assoc])

private theorem diagonal_inner (g : Signs) (v w : SquareSummable) :
    inner ℂ (diagonal g v) (diagonal g w) = inner ℂ v w := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun n => ?_
  change inner ℂ (sign (g n) * v n) (sign (g n) * w n) = inner ℂ (v n) (w n)
  rcases Int.units_eq_one_or (g n) with h | h <;> simp [h, sign]

private theorem diagonal_continuous [DiscreteTopology ℤˣ] (v : SquareSummable) :
    Continuous (fun g : Signs => diagonal g v) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro g
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  have approximation :
      ∀ᶠ s : Finset ℕ in atTop, dist (∑ i ∈ s, lp.single 2 i (v i)) v < ε / 2 :=
    Metric.tendsto_nhds.mp (lp.hasSum_single (by simp) v) (ε / 2) (half_pos hε)
  obtain ⟨s, hs⟩ := approximation.exists
  let w := ∑ i ∈ s, lp.single 2 i (v i)
  have hevent : ∀ᶠ h : Signs in 𝓝 g, ∀ i ∈ s, h i = g i := by
    apply (Filter.eventually_all_finset s).mpr
    intro i _
    have hcoordinate : Continuous (fun h : Signs => h i) := continuous_apply i
    have hopen : IsOpen {h : Signs | h i = g i} :=
      hcoordinate.isOpen_preimage _ (isOpen_discrete ({g i} : Set ℤˣ))
    exact hopen.mem_nhds rfl
  filter_upwards [hevent] with h hh
  have hw : diagonal h w = diagonal g w := by
    dsimp only [w]
    rw [map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply lp.ext
    funext j
    change sign (h j) * (lp.single 2 i (v i) : SquareSummable) j =
      sign (g j) * (lp.single 2 i (v i) : SquareSummable) j
    by_cases hji : j = i
    · subst j
      rw [hh i hi]
    · simp only [lp.single_apply_ne (E := fun _ : ℕ => ℂ) 2 i (v i) hji, mul_zero]
  have hdist (k : Signs) (x y : SquareSummable) :
      dist (diagonal k x) (diagonal k y) = dist x y :=
    ((diagonal k).isometryOfInner (diagonal_inner k)).isometry.dist_eq x y
  calc
    dist (diagonal h v) (diagonal g v) ≤
        dist (diagonal h v) (diagonal h w) + dist (diagonal h w) (diagonal g v) :=
      dist_triangle _ _ _
    _ = dist v w + dist w v := by rw [hdist, hw, hdist]
    _ < ε := by rw [dist_comm v w]; linarith

private def everyCoordinateNonzero : SquareSummable := by
  refine ⟨fun n => (1 / 2 : ℂ) ^ n, memℓp_gen ?_⟩
  have hs : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  convert hs using 1
  funext n
  have h : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [norm_pow, h, ENNReal.toReal_ofNat, Real.rpow_two, ← pow_mul, Nat.mul_comm n 2, pow_mul]
  norm_num

private theorem signRepresentation_nonsmooth : ¬ IsSmooth signRepresentation := by
  intro hs
  obtain ⟨K, hK⟩ := hs everyCoordinateNonzero
  let flip (n : ℕ) : Signs := Function.update 1 n (-1)
  have hlim : Tendsto flip atTop (𝓝 (1 : Signs)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop i] with n hn
    exact (Function.update_of_ne (ne_of_lt hn) _ _).symm
  obtain ⟨n, hn⟩ := (hlim.eventually (K.isOpen.mem_nhds K.one_mem)).exists
  have h := congrArg (fun v : SquareSummable => v n) (hK ⟨flip n, hn⟩)
  change sign (flip n n) * everyCoordinateNonzero n = everyCoordinateNonzero n at h
  have hnegative : (-1 : ℂ) * everyCoordinateNonzero n = 1 * everyCoordinateNonzero n := by
    simpa [flip, sign] using h
  have hnonzero : everyCoordinateNonzero n ≠ 0 := pow_ne_zero _ (by norm_num)
  exact (by norm_num : (-1 : ℂ) ≠ 1) (mul_right_cancel₀ hnonzero hnegative)

/-- The sign group acts continuously by isometries on `ℓ²(ℕ, ℂ)`, with a
vector fixed by no open subgroup. -/
theorem continuousUnitaryNonsmoothCounterexample :
    ContinuousUnitaryNonsmoothCounterexampleStatement := by
  intro h
  have : Finite ℤˣ := Finite.of_surjective (fun b : Bool => if b then 1 else -1) (by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨true, rfl⟩
    · exact ⟨false, rfl⟩)
  exact signRepresentation_nonsmooth
    (h Signs SquareSummable signRepresentation diagonal_continuous diagonal_inner)

end Langlands.Renard.CompactRepresentation
