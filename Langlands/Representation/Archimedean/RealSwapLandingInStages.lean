import Langlands.Representation.Archimedean.RealInductionStagesSlice
import Langlands.Representation.Archimedean.RealSwapLandingIntegral
import Langlands.Representation.Archimedean.RealSwapLandingMirror

/-!
# Landing of consecutive block multipliers in arbitrary ambient rank

Slices in three consecutive coordinates transport the proved GL₃ landing theorem to
arbitrary surrounding block lists. The intermediate functions need only be continuous.
-/

noncomputable section

open scoped Matrix Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean RealBlockMultiplier

namespace RealSwapLandingInStages

set_option backward.isDefEq.respectTransparency false

open InductionStages

variable {n a r : ℕ}

/-- The middle-coordinate embedding is continuous. -/
theorem continuous_blockEmb (h : a + r ≤ n) : Continuous (blockEmb h) := by
  have hc : Continuous (blockMat n a r) :=
    continuous_const.add
      ((continuous_const.matrix_mul (continuous_id.sub continuous_const)).matrix_mul continuous_const)
  exact Units.continuous_iff.mpr
    ⟨hc.comp Units.continuous_val, hc.comp Units.continuous_coe_inv⟩

/-- Slices preserve continuity, without requiring smoothness of the input. -/
theorem continuous_slice (h : a + r ≤ n) (κ : Langlands.GeneralLinear n ℝ)
    {F : Langlands.GeneralLinear n ℝ → ℂ} (hF : Continuous F) :
    Continuous (slice h κ F) := by
  have hc : Continuous (slice h κ (fun _ => (1 : ℂ))) :=
    (contMDiff_slice h κ contMDiff_const).continuous
  have hν : Continuous (sliceFactor n a r) := by
    change Continuous (fun g => sliceFactor n a r g * (1 : ℂ)) at hc
    simpa only [mul_one] using hc
  exact hν.mul (hF.comp ((continuous_blockEmb h).mul continuous_const))

/-- A compact multiplier identity restricts to each compact slice. -/
theorem multiplier_slice (h : a + r ≤ n) {p : ℕ} (hp : p + 1 < r)
    {F H : Langlands.GeneralLinear n ℝ → ℂ} {μ : ℤ → ℂ}
    (hμ : ∀ g ∈ unitaryCompact ℝ n, ∀ k : ℤ,
      blockFourierCoefficient n (a + p) k H g =
        μ k * blockFourierCoefficient n (a + p) k F g)
    {κ : Langlands.GeneralLinear n ℝ} (hκ : κ ∈ unitaryCompact ℝ n) :
    ∀ g ∈ unitaryCompact ℝ r, ∀ k : ℤ,
      blockFourierCoefficient r p k (slice h κ H) g =
        μ k * blockFourierCoefficient r p k (slice h κ F) g := by
  intro g hg k
  rw [blockFourierCoefficient_slice h hp, blockFourierCoefficient_slice h hp,
    hμ _ ((unitaryCompact ℝ n).mul_mem (blockEmb_mem_unitaryCompact h hg) hκ) k]
  ring

/-- The slice coefficient at the identity is the original ambient coefficient. -/
theorem blockFourierCoefficient_slice_one (h : a + r ≤ n) {p : ℕ} (hp : p + 1 < r)
    (κ : Langlands.GeneralLinear n ℝ) (F : Langlands.GeneralLinear n ℝ → ℂ) (k : ℤ) :
    blockFourierCoefficient r p k (slice h κ F) 1 =
      blockFourierCoefficient n (a + p) k F κ := by
  rw [blockFourierCoefficient_slice h hp, sliceFactor_one, map_one, one_mul, one_mul]

end RealSwapLandingInStages

/-- Induced-first GL₃ landing, with arbitrary surrounding blocks and ambient rank. -/
def RealSwapLandingInducedFirstInStagesStatement : Prop :=
  ∀ (n : ℕ) (pre post : List RealBlock) (c : RealCharacterData) (d : ComplexCharacterData)
    (δ : ℂ) (μ₀ μ₁ : ℤ → ℂ) (f h u : Langlands.GeneralLinear n ℝ → ℂ),
    realRank pre + 3 + realRank post = n →
    IsRecurrent δ (c.parity.val : ℤ) μ₁ →
    IsSymmetric (c.parity.val : ℤ) ((-1 : ℂ) ^ c.parity.val) μ₁ →
    IsRecurrent (δ + (d.weight.natAbs : ℂ))
      ((d.weight.natAbs + 1 + c.parity.val : ℕ) : ℤ) μ₀ →
    IsSymmetric ((d.weight.natAbs + 1 + c.parity.val : ℕ) : ℤ)
      ((-1 : ℂ) ^ (d.weight.natAbs + 1 + c.parity.val)) μ₀ →
    f ∈ kFiniteFunctions
      (realStandardModule n (pre ++ [RealBlock.induced d, RealBlock.character c] ++ post))
      (unitaryCompact ℝ n) →
    Continuous h → Continuous u →
    (∀ g ∈ unitaryCompact ℝ n, ∀ k : ℤ,
      blockFourierCoefficient n (realRank pre + 1) k h g =
        μ₁ k * blockFourierCoefficient n (realRank pre + 1) k f g) →
    (∀ g ∈ unitaryCompact ℝ n, ∀ k : ℤ,
      blockFourierCoefficient n (realRank pre) k u g =
        μ₀ k * blockFourierCoefficient n (realRank pre) k h g) →
    ∀ g ∈ unitaryCompact ℝ n, ∀ k : ℤ, |k| < |d.weight| →
      blockFourierCoefficient n (realRank pre + 1) k u g = 0

/-- Character-first GL₃ landing, with arbitrary surrounding blocks and ambient rank. -/
def RealSwapLandingCharacterFirstInStagesStatement : Prop :=
  ∀ (n : ℕ) (pre post : List RealBlock) (c : RealCharacterData) (d : ComplexCharacterData)
    (δ : ℂ) (μ₀ μ₁ : ℤ → ℂ) (f h u : Langlands.GeneralLinear n ℝ → ℂ),
    realRank pre + 3 + realRank post = n →
    IsRecurrent δ ((d.weight.natAbs + 1 + c.parity.val : ℕ) : ℤ) μ₀ →
    IsSymmetric ((d.weight.natAbs + 1 + c.parity.val : ℕ) : ℤ)
      ((-1 : ℂ) ^ (d.weight.natAbs + 1 + c.parity.val)) μ₀ →
    IsRecurrent (δ + (d.weight.natAbs : ℂ)) (c.parity.val : ℤ) μ₁ →
    IsSymmetric (c.parity.val : ℤ) ((-1 : ℂ) ^ c.parity.val) μ₁ →
    f ∈ kFiniteFunctions
      (realStandardModule n (pre ++ [RealBlock.character c, RealBlock.induced d] ++ post))
      (unitaryCompact ℝ n) →
    Continuous h → Continuous u →
    (∀ g ∈ unitaryCompact ℝ n, ∀ k : ℤ,
      blockFourierCoefficient n (realRank pre) k h g =
        μ₀ k * blockFourierCoefficient n (realRank pre) k f g) →
    (∀ g ∈ unitaryCompact ℝ n, ∀ k : ℤ,
      blockFourierCoefficient n (realRank pre + 1) k u g =
        μ₁ k * blockFourierCoefficient n (realRank pre + 1) k h g) →
    ∀ g ∈ unitaryCompact ℝ n, ∀ k : ℤ, |k| < |d.weight| →
      blockFourierCoefficient n (realRank pre) k u g = 0

/-- Both directions of landing in any consecutive three-coordinate slice. -/
def RealSwapLandingInStagesStatement : Prop :=
  RealSwapLandingInducedFirstInStagesStatement ∧ RealSwapLandingCharacterFirstInStagesStatement

namespace RealSwapLandingInStages

open InductionStages

/-- Localization of the induced-first statement by compact slices. -/
theorem inducedFirst_of (hLand : RealSwapLandingInducedFirstStatement) :
    RealSwapLandingInducedFirstInStagesStatement := by
  intro n pre post c d δ μ₀ μ₁ f h u hr hrec₁ hsym₁ hrec₀ hsym₀ hf hh hu h₁ h₀ κ hκ k hk
  have hEmb : realRank pre + 3 ≤ n := by omega
  have hf' : slice hEmb κ f ∈ kFiniteFunctions
      (realStandardModule 3 [RealBlock.induced d, RealBlock.character c])
      (unitaryCompact ℝ 3) :=
    slice_mem_kFin hEmb rfl (by simp [realRank, RealBlock.rank]) hκ hf
  have h₁' := multiplier_slice hEmb (by decide : 1 + 1 < 3) h₁ hκ
  have h₀' := multiplier_slice hEmb (by decide : 0 + 1 < 3)
    (by simpa only [Nat.add_zero] using h₀) hκ
  have hz := hLand c d δ μ₀ μ₁ (slice hEmb κ f) (slice hEmb κ h) (slice hEmb κ u)
    hrec₁ hsym₁ hrec₀ hsym₀ hf' (continuous_slice hEmb κ hh) (continuous_slice hEmb κ hu)
    h₁' h₀' 1 ((unitaryCompact ℝ 3).one_mem) k hk
  rwa [blockFourierCoefficient_slice_one hEmb (by decide : 1 + 1 < 3)] at hz

/-- Localization of the character-first statement by compact slices. -/
theorem characterFirst_of (hLand : RealSwapLandingCharacterFirstStatement) :
    RealSwapLandingCharacterFirstInStagesStatement := by
  intro n pre post c d δ μ₀ μ₁ f h u hr hrec₀ hsym₀ hrec₁ hsym₁ hf hh hu h₀ h₁ κ hκ k hk
  have hEmb : realRank pre + 3 ≤ n := by omega
  have hf' : slice hEmb κ f ∈ kFiniteFunctions
      (realStandardModule 3 [RealBlock.character c, RealBlock.induced d])
      (unitaryCompact ℝ 3) :=
    slice_mem_kFin hEmb rfl (by simp [realRank, RealBlock.rank]) hκ hf
  have h₀' := multiplier_slice hEmb (by decide : 0 + 1 < 3)
    (by simpa only [Nat.add_zero] using h₀) hκ
  have h₁' := multiplier_slice hEmb (by decide : 1 + 1 < 3) h₁ hκ
  have hz := hLand c d δ μ₀ μ₁ (slice hEmb κ f) (slice hEmb κ h) (slice hEmb κ u)
    hrec₀ hsym₀ hrec₁ hsym₁ hf' (continuous_slice hEmb κ hh) (continuous_slice hEmb κ hu)
    h₀' h₁' 1 ((unitaryCompact ℝ 3).one_mem) k hk
  simpa only [blockFourierCoefficient_slice_one hEmb (by decide : 0 + 1 < 3), Nat.add_zero]
    using hz

/-- Both ambient statements follow from their GL₃ counterparts. -/
theorem of_landing (hLand : RealSwapLandingStatement) : RealSwapLandingInStagesStatement :=
  ⟨inducedFirst_of hLand.1, characterFirst_of hLand.2⟩

/-- Landing in arbitrary ambient rank, with no landing premise left over. -/
theorem realSwapLandingInStages : RealSwapLandingInStagesStatement :=
  of_landing ⟨RealSwapLandingIntegral.inducedFirst,
    RealSwapLandingMirror.characterFirst_of_inducedFirst RealSwapLandingIntegral.inducedFirst⟩

end RealSwapLandingInStages

end Langlands.Archimedean
