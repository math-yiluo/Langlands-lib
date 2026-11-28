import Langlands.Representation.Shahidi.OpenCellHeckeRelation
import Langlands.Representation.Whittaker.TwoBlockJacquetCovarianceProof

/-! # The Jacquet function of a lifted Levi function

For a Levi function `Φ` on `GL_(r+1)(K) × GL_(t+1)(K)` with lift `F`, the Jacquet function is
`J(g) = ∫ F(w u'(Y) g) conj ψ(Y_(t,0)) dY` (Bochner integral for the Haar measure `matrixHaar`
with `vol(M(𝒪)) = 1`). For a Levi-invariant `Φ` it is right invariant under
`GL((r+1)+(t+1), 𝒪)` and, if `Φ` is moreover equivariant under the standard characters of the
two blocks, it transforms under the upper unipotent group by the standard character;
integrability of the integrand is preserved by these translations. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell

open Langlands.GeneralLinear Langlands.Conductor Langlands.Unramified.MinusculeCosets
open Langlands.GeneralLinear.Iwasawa MeasureTheory
open scoped ENNReal NNReal

universe u

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p}

local instance ocJacquetTopologicalSpace : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology
local instance ocJacquetValuativeRel : ValuativeRel K.Carrier :=
  K.canonicalTopologicalData.valuativeRel
local instance ocJacquetLocalField : IsNonarchimedeanLocalField K.Carrier :=
  K.canonicalTopologicalData.localField
local instance ocJacquetT2Space : T2Space K.Carrier := K.canonicalTopologicalData.fieldT2
local instance ocJacquetSecondCountableTopology : SecondCountableTopology K.Carrier :=
  K.canonicalTopologicalData.secondCountableTopology
local instance ocJacquetMeasurableSpace : MeasurableSpace K.Carrier := borel K.Carrier
local instance ocJacquetBorelSpace : BorelSpace K.Carrier := ⟨rfl⟩

variable (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter K.Carrier _
  K.canonicalTopologicalData.topology)
variable {ϖ : K.Carrierˣ} (hϖ : Iwasawa.IsUniformizingElement
    (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel) ϖ)
variable {r t : ℕ}

/-- The integrand `Y ↦ conj ψ(Y_(t,0)) F(w u'(Y) g)` of the Jacquet function at `g`. -/
def jacquetIntegrandAt (Φ : Langlands.GeneralLinear (r + 1) K.Carrier →
      Langlands.GeneralLinear (t + 1) K.Carrier → ℂ)
    (g : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) :
    Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier → ℂ :=
  jacquetIntegrand r t ψ LinearMap.id (fun h => liftFunction hϖ Φ (h * g))

/-- The Jacquet function `J(g) = ∫ F(w u'(Y) g) conj ψ(Y_(t,0)) dY` of the lift of `Φ`. -/
def jacquetFunction (Φ : Langlands.GeneralLinear (r + 1) K.Carrier →
      Langlands.GeneralLinear (t + 1) K.Carrier → ℂ)
    (g : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) : ℂ :=
  ∫ Y, jacquetIntegrandAt ψ hϖ Φ g Y ∂matrixHaar K (t + 1) (r + 1)

variable {Φ : Langlands.GeneralLinear (r + 1) K.Carrier →
    Langlands.GeneralLinear (t + 1) K.Carrier → ℂ}

theorem jacquetIntegrandAt_apply (g : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier)
    (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier) :
    jacquetIntegrandAt ψ hϖ Φ g Y = intertwiningJacquetKernel r t ψ Y *
      liftFunction hϖ Φ (blockWeyl (r + 1) (t + 1) K.Carrier *
        intertwiningUnipotent (r + 1) (t + 1) K.Carrier Y * g) := rfl

theorem jacquetIntegrandAt_mul_integral (hΦ : IsLeviInvariant Φ)
    (g k : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier)
    (hk : k ∈ integralSubgroup K.canonicalTopologicalData.Integers (r + 1 + t)) :
    jacquetIntegrandAt ψ hϖ Φ (g * k) = jacquetIntegrandAt ψ hϖ Φ g := by
  funext Y
  rw [jacquetIntegrandAt_apply, jacquetIntegrandAt_apply, ← mul_assoc,
    liftFunction_mul_integral hϖ hΦ _ k hk]

/-- The Jacquet function of a Levi-invariant `Φ` is right invariant under `GL((r+1)+(t+1), 𝒪)`. -/
theorem jacquetFunction_mul_integral (hΦ : IsLeviInvariant Φ)
    (g k : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier)
    (hk : k ∈ integralSubgroup K.canonicalTopologicalData.Integers (r + 1 + t)) :
    jacquetFunction ψ hϖ Φ (g * k) = jacquetFunction ψ hϖ Φ g := by
  rw [jacquetFunction, jacquetIntegrandAt_mul_integral ψ hϖ hΦ g k hk]
  rfl

theorem jacquetIntegrandAt_intertwiningUnipotent_mul
    (y : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier)
    (g : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) :
    jacquetIntegrandAt ψ hϖ Φ (intertwiningUnipotent (r + 1) (t + 1) K.Carrier y * g) =
      jacquetIntegrand r t ψ LinearMap.id
        (fun h => (fun h' => liftFunction hϖ Φ (h' * g))
          (h * intertwiningUnipotent (r + 1) (t + 1) K.Carrier y)) := by
  funext Y
  simp only [jacquetIntegrandAt, jacquetIntegrand_apply, mul_assoc]

/-- Translation by the exchanged radical multiplies the Jacquet function by the intertwining
character `ψ(y_(t,0))` (no hypothesis on `Φ`). -/
theorem jacquetFunction_intertwiningUnipotent_mul
    (y : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier)
    (g : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) :
    jacquetFunction ψ hϖ Φ (intertwiningUnipotent (r + 1) (t + 1) K.Carrier y * g) =
      (intertwiningCharacter r t ψ (Multiplicative.ofAdd y) : ℂ) *
        jacquetFunction ψ hϖ Φ g := by
  have h := integral_jacquetIntegrand_rightTranslate_intertwiningUnipotent ψ r t LinearMap.id
    (matrixHaar K (t + 1) (r + 1)) (fun h => liftFunction hϖ Φ (h * g)) y
  unfold jacquetFunction jacquetIntegrandAt
  simp only [mul_assoc] at h ⊢
  exact h

theorem integrable_jacquetIntegrandAt_intertwiningUnipotent_mul
    (y : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier)
    (g : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier)
    (hi : Integrable (jacquetIntegrandAt ψ hϖ Φ g) (matrixHaar K (t + 1) (r + 1))) :
    Integrable (jacquetIntegrandAt ψ hϖ Φ
      (intertwiningUnipotent (r + 1) (t + 1) K.Carrier y * g))
      (matrixHaar K (t + 1) (r + 1)) := by
  have h := integrable_jacquetIntegrand_rightTranslate_intertwiningUnipotent ψ r t LinearMap.id
    (matrixHaar K (t + 1) (r + 1)) (fun h => liftFunction hϖ Φ (h * g)) y hi
  unfold jacquetIntegrandAt
  simp only [mul_assoc] at h ⊢
  exact h

include hϖ in
theorem determinantNorm_upperUnipotent {n : ℕ} (u : upperUnipotent n K.Carrier) :
    K.canonicalTopologicalData.determinantNorm n u.val = 1 := by
  have h := determinantNorm_unipotent_mul hϖ u.2 1
  rw [mul_one, map_one, Units.val_one, NNReal.coe_one] at h
  have h' : ((K.canonicalTopologicalData.determinantNorm n u.val : ℝ≥0) : ℝ) = 1 := by
    simpa using h
  exact Units.ext (NNReal.coe_injective (by simpa using h'))

include hϖ in
theorem map_matrixHaar_rectangularConj_unipotent (u₁ : upperUnipotent (r + 1) K.Carrier)
    (u₂ : upperUnipotent (t + 1) K.Carrier) :
    (matrixHaar K (t + 1) (r + 1)).map (rectangularConj u₂.val u₁.val) =
      matrixHaar K (t + 1) (r + 1) := by
  rw [map_rectangularConj_padic K K.canonicalTopologicalData (matrixHaar K (t + 1) (r + 1))
    u₂.val u₁.val, determinantNorm_upperUnipotent hϖ, determinantNorm_upperUnipotent hϖ]
  simp

variable {θ₁ : upperUnipotent (r + 1) K.Carrier →* ℂˣ} {θ₂ : upperUnipotent (t + 1) K.Carrier →* ℂˣ}

theorem liftFunction_blockSum_unipotent_mul (hΦ : IsLeviInvariant Φ)
    (hθ : IsLeviEquivariant θ₁ θ₂ Φ) (u₁ : upperUnipotent (r + 1) K.Carrier)
    (u₂ : upperUnipotent (t + 1) K.Carrier) (h : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) :
    liftFunction hϖ Φ (blockSum (u₁.val, u₂.val) * h) =
      ((θ₁ u₁ : ℂ) * (θ₂ u₂ : ℂ)) * liftFunction hϖ Φ h := by
  have hu := blockSum_mem_upperUnipotent u₁.2 u₂.2
  rw [liftFunction_unipotent_mul hϖ hΦ hθ hu]
  have e1 : (⟨topLeft (blockSum (u₁.val, u₂.val)) hu.1, topLeft_mem_upperUnipotent hu⟩ :
      upperUnipotent (r + 1) K.Carrier) = u₁ := Subtype.ext (topLeft_blockSum hu.1)
  have e2 : (⟨botRight (blockSum (u₁.val, u₂.val)) hu.1, botRight_mem_upperUnipotent hu⟩ :
      upperUnipotent (t + 1) K.Carrier) = u₂ := Subtype.ext (botRight_blockSum hu.1)
  rw [e1, e2]

/-- For a Levi-invariant `Φ` that is Levi-equivariant for `θ₁`, `θ₂`, translation by the
exchanged unipotent Levi multiplies by `θ₁(u₁) θ₂(u₂)`. -/
theorem jacquetFunction_levi_mul (hΦ : IsLeviInvariant Φ) (hθ : IsLeviEquivariant θ₁ θ₂ Φ)
    (u₁ : upperUnipotent (r + 1) K.Carrier) (u₂ : upperUnipotent (t + 1) K.Carrier)
    (g : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) :
    jacquetFunction ψ hϖ Φ
        (swapRank (r + 1) (t + 1) K.Carrier (blockSum (u₂.val, u₁.val)) * g) =
      ((θ₁ u₁ : ℂ) * (θ₂ u₂ : ℂ)) * jacquetFunction ψ hϖ Φ g := by
  have h := integral_jacquetIntegrand_rightTranslate_unipotent_blockSum ψ LinearMap.id
    (matrixHaar K (t + 1) (r + 1)) u₁ u₂ ((θ₁ u₁ : ℂ) * (θ₂ u₂ : ℂ))
    (fun h => liftFunction hϖ Φ (h * g))
    (fun h => by
      simpa only [LinearMap.id_apply, mul_assoc] using
        liftFunction_blockSum_unipotent_mul hϖ hΦ hθ u₁ u₂ (h * g))
    (map_matrixHaar_rectangularConj_unipotent hϖ u₁ u₂)
  unfold jacquetFunction jacquetIntegrandAt
  simp only [mul_assoc] at h ⊢
  exact h

theorem integrable_jacquetIntegrandAt_levi_mul (hΦ : IsLeviInvariant Φ)
    (hθ : IsLeviEquivariant θ₁ θ₂ Φ)
    (u₁ : upperUnipotent (r + 1) K.Carrier) (u₂ : upperUnipotent (t + 1) K.Carrier)
    (g : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier)
    (hi : Integrable (jacquetIntegrandAt ψ hϖ Φ g) (matrixHaar K (t + 1) (r + 1))) :
    Integrable (jacquetIntegrandAt ψ hϖ Φ
      (swapRank (r + 1) (t + 1) K.Carrier (blockSum (u₂.val, u₁.val)) * g))
      (matrixHaar K (t + 1) (r + 1)) := by
  have h := integrable_jacquetIntegrand_rightTranslate_unipotent_blockSum ψ LinearMap.id
    (matrixHaar K (t + 1) (r + 1)) u₁ u₂ ((θ₁ u₁ : ℂ) * (θ₂ u₂ : ℂ))
    (fun h => liftFunction hϖ Φ (h * g))
    (fun h => by
      simpa only [LinearMap.id_apply, mul_assoc] using
        liftFunction_blockSum_unipotent_mul hϖ hΦ hθ u₁ u₂ (h * g))
    (map_matrixHaar_rectangularConj_unipotent hϖ u₁ u₂) hi
  have e : jacquetIntegrandAt ψ hϖ Φ
      (swapRank (r + 1) (t + 1) K.Carrier (blockSum (u₂.val, u₁.val)) * g) =
      jacquetIntegrand r t ψ LinearMap.id (fun h => (fun h' => liftFunction hϖ Φ (h' * g))
        (h * swapRank (r + 1) (t + 1) K.Carrier (blockSum (u₂.val, u₁.val)))) := by
    funext Y
    simp only [jacquetIntegrandAt, jacquetIntegrand_apply, mul_assoc]
  rw [e]
  exact h

/-- **Upper unipotent covariance of the Jacquet function**, for a Levi-invariant `Φ` that is
Levi-equivariant for the standard characters. -/
theorem jacquetFunction_unipotent_mul (hΦ : IsLeviInvariant Φ)
    (hθ : IsLeviEquivariant (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ r)
      (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ t) Φ)
    (u : upperUnipotent ((r + 1) + (t + 1)) K.Carrier)
    (g : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) :
    jacquetFunction ψ hϖ Φ (u.val * g) =
      (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ (r + 1 + t) u : ℂ) *
        jacquetFunction ψ hϖ Φ g := by
  obtain ⟨u₁, u₂, y, hu⟩ :=
    Whittaker.upperUnipotent_exchanged_factorization (Nat.succ_pos r) (Nat.succ_pos t) u
  rw [hu, mul_assoc, jacquetFunction_levi_mul ψ hϖ hΦ hθ,
    jacquetFunction_intertwiningUnipotent_mul]
  let du : upperUnipotent ((r + 1) + (t + 1)) K.Carrier :=
    ⟨swapRank (r + 1) (t + 1) K.Carrier (blockSum (u₂.val, u₁.val)),
      swapRank_mem_upperUnipotent _ _ _ (Whittaker.blockSum_mem_upperUnipotent u₂ u₁)⟩
  let ny := intertwiningToUnipotent (r + 1) (t + 1) K.Carrier (Multiplicative.ofAdd y)
  have hu' : u = du * ny := Subtype.ext hu
  rw [hu', map_mul, Units.val_mul, Whittaker.standardCharacter_exchanged_blockSum]
  rw [← mul_assoc]
  rfl

theorem integrable_jacquetIntegrandAt_unipotent_mul (hΦ : IsLeviInvariant Φ)
    (hθ : IsLeviEquivariant (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ r)
      (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ t) Φ)
    (u : upperUnipotent ((r + 1) + (t + 1)) K.Carrier)
    (g : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier)
    (hi : Integrable (jacquetIntegrandAt ψ hϖ Φ g) (matrixHaar K (t + 1) (r + 1))) :
    Integrable (jacquetIntegrandAt ψ hϖ Φ (u.val * g)) (matrixHaar K (t + 1) (r + 1)) := by
  obtain ⟨u₁, u₂, y, hu⟩ :=
    Whittaker.upperUnipotent_exchanged_factorization (Nat.succ_pos r) (Nat.succ_pos t) u
  rw [hu, mul_assoc]
  exact integrable_jacquetIntegrandAt_levi_mul ψ hϖ hΦ hθ u₁ u₂ _
    (integrable_jacquetIntegrandAt_intertwiningUnipotent_mul ψ hϖ y g hi)

end Langlands.Shahidi.OpenCell
