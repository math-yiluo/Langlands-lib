import Langlands.Global.RankinSelberg.RealBlockSmoothExtension
import Langlands.Representation.Archimedean.RealInductionStagesSlice
import Langlands.Representation.Archimedean.RealSwapLandingAlgebra
import Langlands.Representation.Archimedean.SmoothRealGroupIntertwining

/-! # Real block Fourier multipliers on smooth slices -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach

open DerivativeSmoothVectors RealBlockFrobeniusMap RealBlockMultiplier InductionStages

private local instance (n : ℕ) (ds : List RealBlock) : NormedAddCommGroup (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedAddCommGroup

private local instance (n : ℕ) (ds : List RealBlock) : NormedSpace ℂ (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedSpace

local notation "G" => fun n : ℕ => Langlands.GeneralLinear n ℝ
local notation:max "D" rank:max ds:max => DerivativeSmoothVectors (matrixModel ℝ rank) (representation (n := rank) ds)
local notation:max "act" rank:max ds:max => DerivativeSmoothVectors.representation (matrixModel ℝ rank)
  (representation (n := rank) ds)
local notation:max "V" n:max ds:max => Automorphic.realStandardKFinite n ds
local notation:max "F" ds:max v:max => Subtype.val (LinearEquiv.symm (derivativeEquiv ds) v)

private theorem continuous_blockFourierCoefficient_eval {n : ℕ} (ds : List RealBlock)
    (p : ℕ) (k : ℤ) (g : G n) : Continuous fun v : D n ds => blockFourierCoefficient n p k (F ds v) g := by
  let P := derivativeCLM (matrixModel ℝ n) (representation (n := n) ds) []
  have he (v : D n ds) : F ds v = extensionOfProfile ds (P v).val := by
    obtain ⟨f, rfl⟩ := (derivativeEquiv ds).surjective v
    simp only [P, derivativeCLM_apply, iteratedLieDerivative_nil, toSmooth_derivativeEquiv,
      embed_val, extensionOfProfile_restriction, LinearEquiv.symm_apply_apply]
  simp_rw [he]
  unfold blockFourierCoefficient
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (v : D n ds) (θ : ℝ) => extensionOfProfile ds (P v).val (blockRotation n p θ * g) *
      Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I))) ?_ _ _
  have hP : Continuous (fun x : D n ds × ℝ => (P x.1).val) :=
    continuous_subtype_val.comp (P.continuous.comp continuous_fst)
  have hG : Continuous (fun x : D n ds × ℝ => blockRotation n p x.2 * g) :=
    ((continuous_blockRotation n p).comp continuous_snd).mul continuous_const
  exact ((continuous_extensionOfProfile ds).comp (hP.prodMk hG)).mul
    (Complex.continuous_exp.comp (by fun_prop))

private theorem reconstruct_act {n : ℕ} (ds : List RealBlock) (g : G n) (v : D n ds) :
    F ds (act n ds g v) = Whittaker.rightTranslation ℂ (G n) g (F ds v) := by
  obtain ⟨f, rfl⟩ := (derivativeEquiv ds).surjective v
  rw [← derivativeEquiv_translate, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  rfl

/-- The fixed symbol multiplies the Fourier coefficient at every real group element. -/
def IsSmoothBlockFourierMultiplier {n : ℕ} {ds es : List RealBlock} (p : ℕ) (μ : ℤ → ℂ)
    (T : D n ds →L[ℂ] D n es) : Prop :=
  ∀ (k : ℤ) (g : G n) (v : D n ds),
    blockFourierCoefficient n p k (F es (T v)) g = μ k * blockFourierCoefficient n p k (F ds v) g

private theorem isSmoothBlockFourierMultiplier_of_agrees {r p : ℕ} {ds es : List RealBlock}
    {ε : ℤ} {σ : ℂ} {μ : ℤ → ℂ} (h : IsBlockFrobData (r + 1) ds es p ε σ μ)
    (T : D (r + 1) ds →L[ℂ] D (r + 1) es)
    (hT : ∀ f : V (r + 1) ds, T (compactFiniteEquiv ds f).val = (compactFiniteEquiv es (blockFrobMap h f)).val)
    (hG : ∀ g v, T (act (r + 1) ds g v) = act (r + 1) es g (T v)) :
    IsSmoothBlockFourierMultiplier p μ T := by
  intro k g v
  have h₁ : ∀ w : D (r + 1) ds, blockFourierCoefficient (r + 1) p k (F es (T w)) 1 =
      μ k * blockFourierCoefficient (r + 1) p k (F ds w) 1 := by
    have he := (denseRange_compactFiniteEquiv (r := r) ds).equalizer
      ((continuous_blockFourierCoefficient_eval es p k 1).comp T.continuous)
      (continuous_const.mul (continuous_blockFourierCoefficient_eval ds p k 1))
      (funext fun f => by
        change blockFourierCoefficient (r + 1) p k (F es (T (compactFiniteEquiv ds f).val)) 1 =
          μ k * blockFourierCoefficient (r + 1) p k (F ds (compactFiniteEquiv ds f).val) 1
        rw [hT]
        simp only [compactFiniteEquiv_val, LinearEquiv.symm_apply_apply]
        exact blockFourierCoefficient_blockFrobMap h f ((unitaryCompact ℝ (r + 1)).one_mem) k)
    exact congrFun he
  have hw := h₁ (act (r + 1) ds g v)
  rw [hG, reconstruct_act, reconstruct_act, blockFourierCoefficient_rightTranslation,
    blockFourierCoefficient_rightTranslation, one_mul] at hw
  exact hw

/-- The recurrent polynomially bounded Frobenius multiplier extends to the smooth
carriers, intertwines the full action and retains its Fourier symbol at every point. -/
def RealSmoothBlockFourierMultiplierStatement : Prop :=
  ∀ (r p d : ℕ) (ds es : List RealBlock) (ε : ℤ) (σ : ℂ) (μ : ℤ → ℂ)
    (h : IsBlockFrobData (r + 1) ds es p ε σ μ),
    IsRecurrent (GramFormula.realPositionExponent ds p - GramFormula.realPositionExponent ds (p + 1) + 1) ε μ →
    ∀ C : ℝ, 0 ≤ C → (∀ j, ‖μ j‖ ≤ C * (max 1 |(j : ℝ)|) ^ d) →
      ∃ T : D (r + 1) ds →L[ℂ] D (r + 1) es,
        (∀ f : V (r + 1) ds,
          T (compactFiniteEquiv ds f).val = (compactFiniteEquiv es (blockFrobMap h f)).val) ∧
        (∀ g v, T (act (r + 1) ds g v) = act (r + 1) es g (T v)) ∧
        IsSmoothBlockFourierMultiplier p μ T

theorem realSmoothBlockFourierMultiplier : RealSmoothBlockFourierMultiplierStatement := by
  intro r p d ds es ε σ μ h hrec C hC hμ
  obtain ⟨T, hT, hLie, hK⟩ := exists_continuous_blockFrobMap h hrec d hC hμ
  have hG := map_representation_real_of_compact_and_lie _ _
    (isContinuousRepresentation ds) (isContinuousRepresentation es) T hLie hK
  exact ⟨T, hT, hG, isSmoothBlockFourierMultiplier_of_agrees h T hT hG⟩

/-- The normalized Levi slice of a genuine smooth real standard vector. -/
def smoothStandardSlice {n a m : ℕ} {pre ds post : List RealBlock}
    (h : a + m ≤ n) (ha : realRank pre = a) (hm : realRank ds = m) (κ : G n)
    (v : D n (pre ++ ds ++ post)) : D m ds :=
  derivativeEquiv ds ⟨slice h κ (F (pre ++ ds ++ post) v),
    slice_mem_realStandardModule h ha hm κ ((derivativeEquiv (pre ++ ds ++ post)).symm v).property⟩

@[simp] theorem reconstruct_smoothStandardSlice {n a m : ℕ} {pre ds post : List RealBlock}
    (h : a + m ≤ n) (ha : realRank pre = a) (hm : realRank ds = m) (κ : G n)
    (v : D n (pre ++ ds ++ post)) :
    F ds (smoothStandardSlice h ha hm κ v) = slice h κ (F (pre ++ ds ++ post) v) := by
  rw [smoothStandardSlice, LinearEquiv.symm_apply_apply]

/-- Large and small smooth block operators with the same symbol commute with the
normalized Levi slice at each ambient real group element. -/
theorem smoothBlockFourierMultiplier_slice {n a m p : ℕ} {pre ds es post : List RealBlock}
    {μ : ℤ → ℂ} (h : a + m ≤ n) (ha : realRank pre = a) (hd : realRank ds = m) (he : realRank es = m)
    (hp : p + 1 < m) (T : D n (pre ++ ds ++ post) →L[ℂ] D n (pre ++ es ++ post))
    (S : D m ds →L[ℂ] D m es) (hT : IsSmoothBlockFourierMultiplier (a + p) μ T)
    (hS : IsSmoothBlockFourierMultiplier p μ S) (κ : G n) (v : D n (pre ++ ds ++ post)) :
    smoothStandardSlice h ha he κ (T v) = S (smoothStandardSlice h ha hd κ v) := by
  apply (derivativeEquiv es).symm.injective
  apply Subtype.ext
  funext g
  apply RealSwapLandingAlgebra.eq_of_blockFourierCoefficient_eq hp
    ((derivativeEquiv es).symm _).property.1.1.continuous
    ((derivativeEquiv es).symm _).property.1.1.continuous g
  intro j
  rw [reconstruct_smoothStandardSlice, hS, reconstruct_smoothStandardSlice,
    blockFourierCoefficient_slice h hp, blockFourierCoefficient_slice h hp, hT]
  ring

end Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach
