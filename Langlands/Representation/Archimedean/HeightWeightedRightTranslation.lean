import Langlands.Representation.Archimedean.BanachModerateGrowth
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-! # A continuous right-translation action on height-weighted functions -/

noncomputable section

open Filter Set
open scoped Topology ZeroAtInfty

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.HeightWeightedRightTranslation

variable {A : Type*} [NormedRing A]

local notation "G" => Aˣ
local notation "E" => (Aˣ →C₀ ℂ)

private theorem height_pos (g : G) : 0 < unitHeight g := zero_lt_one.trans_le (one_le_unitHeight g)

private def ratio (d : ℕ) (g x : G) : ℝ := (unitHeight (x * g) / unitHeight x) ^ d

private theorem ratio_nonneg (d : ℕ) (g x : G) : 0 ≤ ratio d g x :=
  pow_nonneg (div_nonneg (height_pos _).le (height_pos _).le) _

private theorem ratio_le (d : ℕ) (g x : G) : ratio d g x ≤ unitHeight g ^ d := by
  apply pow_le_pow_left₀ (div_nonneg (height_pos _).le (height_pos _).le) _ d
  apply (div_le_iff₀ (height_pos x)).mpr
  rw [mul_comm]
  exact unitHeight_mul_le x g

private theorem ratio_mul (d : ℕ) (g h x : G) :
    ratio d (g * h) x = ratio d g x * ratio d h (x * g) := by
  unfold ratio
  rw [← mul_pow, mul_assoc]
  congr 1
  field_simp [(height_pos x).ne', (height_pos (x * g)).ne']

private theorem continuous_ratio (d : ℕ) : Continuous (fun p : G × G => ratio d p.1 p.2) :=
  ((continuous_unitHeight.comp (continuous_snd.mul continuous_fst)).div
    (continuous_unitHeight.comp continuous_snd) (fun p => (height_pos p.2).ne')).pow d

private def kernel (d : ℕ) (F : E) (g x : G) : ℂ := ratio d g x • F (x * g)

private theorem continuous_kernel (d : ℕ) (F : E) :
    Continuous (Function.uncurry (kernel d F)) :=
  (continuous_ratio d).smul (F.continuous_toFun.comp (continuous_snd.mul continuous_fst))

private theorem norm_kernel_le (d : ℕ) (F : E) (g x : G) :
    ‖kernel d F g x‖ ≤ unitHeight g ^ d * ‖F (x * g)‖ := by
  rw [kernel, norm_smul, Real.norm_of_nonneg (ratio_nonneg d g x)]
  exact mul_le_mul_of_nonneg_right (ratio_le d g x) (norm_nonneg _)

private theorem zero_at_infty_kernel (d : ℕ) (F : E) (g : G) :
    Tendsto (kernel d F g) (cocompact G) (𝓝 0) := by
  have hF : Tendsto (fun x : G => F (x * g)) (cocompact G) (𝓝 0) :=
    (zero_at_infty F).comp (Homeomorph.mulRight g).isClosedEmbedding.tendsto_cocompact
  rw [tendsto_zero_iff_norm_tendsto_zero] at hF ⊢
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall (norm_kernel_le d F g))
  simpa only [mul_zero] using tendsto_const_nhds.mul hF

private def vector (d : ℕ) (F : E) (g : G) : E where
  toFun := kernel d F g
  continuous_toFun := (continuous_kernel d F).comp (continuous_const.prodMk continuous_id)
  zero_at_infty' := zero_at_infty_kernel d F g

private theorem norm_vector_le (d : ℕ) (F : E) (g : G) :
    ‖vector d F g‖ ≤ unitHeight g ^ d * ‖F‖ := by
  have hPow : 0 ≤ unitHeight g ^ d := pow_nonneg (height_pos g).le _
  change ‖(vector d F g).toBCF‖ ≤ _
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hPow (norm_nonneg F))).mpr
  intro x
  exact (norm_kernel_le d F g x).trans
    (mul_le_mul_of_nonneg_left (F.toBCF.norm_coe_le_norm (x * g)) hPow)

/-- Right translation on functions represented after division by a power of the height. -/
def representation (d : ℕ) : G →* (E →L[ℂ] E) where
  toFun g := LinearMap.mkContinuous
    { toFun := fun F => vector d F g
      map_add' := fun F F' => ZeroAtInftyContinuousMap.ext fun x => by
        change ratio d g x • (F (x * g) + F' (x * g)) = _
        exact smul_add _ _ _
      map_smul' := fun c F => ZeroAtInftyContinuousMap.ext fun x => by
        change ratio d g x • (c • F (x * g)) = c • (ratio d g x • F (x * g))
        exact smul_comm _ _ _ }
    (unitHeight g ^ d) (fun F => norm_vector_le d F g)
  map_one' := by
    apply ContinuousLinearMap.ext
    intro F
    ext x
    change ratio d 1 x • F (x * 1) = F x
    simp [ratio, (height_pos x).ne']
  map_mul' g h := by
    apply ContinuousLinearMap.ext
    intro F
    ext x
    change ratio d (g * h) x • F (x * (g * h)) = ratio d g x • (ratio d h (x * g) • F (x * g * h))
    rw [ratio_mul, mul_assoc, mul_smul]

@[simp]
theorem representation_apply (d : ℕ) (g : G) (F : E) (x : G) :
    representation d g F x = (unitHeight (x * g) / unitHeight x) ^ d • F (x * g) := rfl

/-- The operator norm of a translation is bounded by the height at its translating element. -/
theorem norm_representation_le (d : ℕ) (g : G) : ‖representation d g‖ ≤ unitHeight g ^ d := by
  exact ContinuousLinearMap.opNorm_le_bound _ (pow_nonneg (height_pos g).le _) fun F =>
    norm_vector_le d F g

variable [ProperSpace A]

/-- Each orbit is continuous in the supremum norm. -/
theorem continuous_orbit (d : ℕ) (F : E) : Continuous (fun g : G => representation d g F) := by
  rw [continuous_iff_continuousAt]
  intro g
  change Tendsto (fun q : G => representation d q F) (𝓝 g) (𝓝 (representation d g F))
  rw [ZeroAtInftyContinuousMap.tendsto_iff_tendstoUniformly, Metric.tendstoUniformly_iff]
  intro ε hε
  let K : Set G := {q | unitHeight q ≤ unitHeight g + 1}
  have hK : IsCompact K := isCompact_unitHeight_sublevel (by linarith [one_le_unitHeight g])
  have hgK : g ∈ K := by dsimp [K]; linarith
  have hKnhds : K ∈ 𝓝 g := continuous_unitHeight.continuousAt (Iic_mem_nhds (lt_add_one _))
  let B := (unitHeight g + 1) ^ d
  have hB : 0 < B := pow_pos (add_pos (height_pos g) zero_lt_one) d
  have hBound (q : G) (hq : q ∈ K) : unitHeight q ^ d ≤ B :=
    pow_le_pow_left₀ (height_pos q).le hq _
  have hSmall : ∀ᶠ x in cocompact G, ‖F x‖ < ε / (4 * B) :=
    (zero_at_infty F).eventually (by
      simpa only [sub_zero] using eventually_norm_sub_lt (0 : ℂ) (div_pos hε (by positivity : 0 < 4 * B)))
  obtain ⟨S, hS, hSsmall⟩ := mem_cocompact.mp hSmall
  let T : Set G := (fun p : G × G => p.1 * p.2⁻¹) '' (S ×ˢ K)
  have hT := (hS.prod hK).image (continuous_fst.mul continuous_snd.inv)
  let U : Set (G × G) := {p | dist (kernel d F g p.2) (kernel d F p.1 p.2) < ε}
  have hOpen : IsOpen U := isOpen_lt
    (((continuous_kernel d F).comp (continuous_const.prodMk continuous_snd)).dist (continuous_kernel d F))
    continuous_const
  have hU : U ∈ (𝓝 g) ×ˢ 𝓝ˢ T := hT.mem_prod_nhdsSet_of_forall fun x _ => by
    rw [← nhds_prod_eq]
    exact hOpen.mem_nhds (by simpa only [U, mem_ofPred_eq, dist_self] using hε)
  obtain ⟨O, hO, V, hV, hUV⟩ := mem_prod_iff.mp hU
  filter_upwards [hO, hKnhds] with q hq hqK
  intro x
  change dist (kernel d F g x) (kernel d F q x) < ε
  by_cases hx : x ∈ T
  · have hxV : x ∈ V := subset_of_mem_nhdsSet hV hx
    have he : (q, x) ∈ U := hUV (show (q, x) ∈ O ×ˢ V from ⟨hq, hxV⟩)
    exact he
  · have hxS (k : G) (hk : k ∈ K) : x * k ∉ S := by
      intro hs
      apply hx
      exact ⟨(x * k, k), ⟨hs, hk⟩, mul_inv_cancel_right x k⟩
    have hm (k : G) (hk : k ∈ K) : ‖kernel d F k x‖ ≤ ε / 4 := by
      calc
        _ ≤ unitHeight k ^ d * ‖F (x * k)‖ := norm_kernel_le d F k x
        _ ≤ B * (ε / (4 * B)) := mul_le_mul (hBound k hk) (hSsmall (hxS k hk)).le (norm_nonneg _) hB.le
        _ = ε / 4 := by field_simp
    exact (dist_le_norm_add_norm _ _).trans_lt (by linarith [hm g hgK, hm q hqK])

/-- The height-weighted action on continuous functions vanishing at infinity is jointly continuous. -/
def HeightWeightedRightTranslationStatement : Prop :=
  ∀ (A : Type*) [NormedRing A] [ProperSpace A] (d : ℕ),
    IsContinuousRepresentation (representation (A := A) d)

theorem heightWeightedRightTranslation : HeightWeightedRightTranslationStatement := by
  intro A _ _ d
  apply continuous_iff_continuousAt.2
  intro p
  apply Metric.tendsto_nhds.2
  intro ε hε
  let B := unitHeight p.1 ^ d + 1
  have hB : 0 < B := add_pos_of_nonneg_of_pos (pow_nonneg (height_pos p.1).le _) zero_lt_one
  have hBound : ∀ᶠ q in 𝓝 p, unitHeight q.1 ^ d < B :=
    ((continuous_unitHeight.comp continuous_fst).pow d).continuousAt
      (Iio_mem_nhds (lt_add_one _))
  have hVec : ∀ᶠ q in 𝓝 p, dist q.2 p.2 < ε / (2 * B) :=
    Metric.tendsto_nhds.1 continuous_snd.continuousAt (ε / (2 * B)) (by positivity)
  have hOrb : ∀ᶠ q in 𝓝 p, dist (representation d q.1 p.2) (representation d p.1 p.2) < ε / 2 :=
    Metric.tendsto_nhds.1 ((continuous_orbit d p.2).comp continuous_fst).continuousAt (ε / 2) (half_pos hε)
  filter_upwards [hBound, hVec, hOrb] with q hq hV hR
  have h : dist (representation d q.1 q.2) (representation d q.1 p.2) ≤ ε / 2 := by
    rw [dist_eq_norm, ← map_sub]
    calc
      _ ≤ ‖representation d q.1‖ * ‖q.2 - p.2‖ := (representation d q.1).le_opNorm _
      _ ≤ B * (ε / (2 * B)) := mul_le_mul ((norm_representation_le d q.1).trans hq.le)
        (by simpa only [dist_eq_norm] using hV.le) (norm_nonneg _) hB.le
      _ = ε / 2 := by field_simp
  exact (dist_triangle _ _ _).trans_lt (by linarith)

end Langlands.Archimedean.HeightWeightedRightTranslation
