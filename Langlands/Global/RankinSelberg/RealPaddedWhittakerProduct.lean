import Langlands.Global.RankinSelberg.RealPaddedExponential
import Langlands.Global.RankinSelberg.RealUnequalConvergence
import Langlands.Representation.Archimedean.SmoothProjectiveProductDensity
import Langlands.Representation.Archimedean.SmoothAction

/-! # Paired real Whittaker forms for the genuine product-group action -/

noncomputable section

open Set
open scoped ContDiff Manifold Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false

namespace Langlands.Global.RankinSelbergGlobal.RealPaddedWhittakerProduct

open Langlands.Archimedean Langlands.Archimedean.DerivativeSmoothVectors
open RealPaddedExponential
open CompletedProjectiveRepresentation

local notation "M" => fun n : ℕ => Matrix (Fin n) (Fin n) ℝ
local notation "G" => fun n : ℕ => Langlands.GeneralLinear (n + 1) ℝ
local notation "N" => fun n : ℕ => Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ

private theorem realWhittakerCharacter_pad_of_le {m n : ℕ} (h : m ≤ n) (a : ℝˣ) (u : G m) :
    realWhittakerCharacter a (padGL (Nat.succ_le_succ h) u) = realWhittakerCharacter a u := by
  obtain hlt | rfl := lt_or_eq_of_le h
  · exact RealUnequalConvergence.realWhittakerCharacter_padGL hlt (Nat.succ_le_succ h) a u
  · congr 1
    apply Units.ext
    ext i j
    rw [UnequalAnalytic.padGL_apply]
    simp only [i.isLt, j.isLt, and_self, dite_true]

variable (n : Fin 2 → ℕ) (E : Fin 2 → Type*)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)] [∀ i, CompleteSpace (E i)]
  (R : ∀ i, G (n i) →* (E i →L[ℂ] E i))

local notation "A" => fun i => M (n i + 1)
local notation "I" => 𝓘(ℝ, (∀ i : Fin 2, A i))
local notation "U" => (∀ i : Fin 2, A i)ˣ
local notation "I₀" => fun i => 𝓘(ℝ, A i)
local notation "D" => DerivativeSmoothVectors I (productAction A R)
local notation "D₀" => fun i => DerivativeSmoothVectors (I₀ i) (R i)

private theorem clm_eq_of_eq_on_pure (hR : ∀ i, IsContinuousRepresentation (R i))
    (S T : D →L[ℂ] ℂ) (h : ∀ v, S (pureSmooth A R v) = T (pureSmooth A R v)) : S = T := by
  apply ContinuousLinearMap.ext
  refine congrFun (Continuous.ext_on (smoothProjectiveProductDensity A E R hR)
    S.continuous T.continuous (fun x hx => ?_))
  have hs : pureSmoothSpan A R ≤ LinearMap.ker (S - T).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v, rfl⟩
    exact LinearMap.mem_ker.mpr (sub_eq_zero.mpr (h v))
  exact sub_eq_zero.mp (LinearMap.mem_ker.mp (hs hx))

/-- The first and second additive scales of a real Whittaker pair. -/
def oppositeScale (a : ℝˣ) (i : Fin 2) : ℝˣ := if i = 0 then a else -a

/-- Opposite-character Whittaker forms extend to a product-group smooth form. Its character on
independent upper unipotents is the product character, which cancels after leading padding. -/
def RealPaddedWhittakerProductStatement : Prop :=
  (∀ i, IsContinuousRepresentation (R i)) →
  ∀ (a : ℝˣ) (L : ∀ i, D₀ i →L[ℂ] ℂ),
    (∀ (i : Fin 2) (u : N (n i)) (v : D₀ i),
      L i (DerivativeSmoothVectors.representation (I₀ i) (R i) u.val v) =
        realWhittakerCharacter (oppositeScale a i) u.val * L i v) →
    ∃ T : D →L[ℂ] ℂ,
      (∀ (v : ∀ i, D₀ i), T (pureSmooth A R v) = ∏ i, L i (v i)) ∧
      (∀ (g : U) (_h : ∀ i, unitProjection A i g ∈ N (n i)) (w : D),
        T (DerivativeSmoothVectors.representation I (productAction A R) g w) =
          (∏ i, realWhittakerCharacter (oppositeScale a i) (unitProjection A i g)) * T w) ∧
      ∀ (m : ℕ) (hm : ∀ i, m ≤ n i) (u : N m) (w : D),
        T (DerivativeSmoothVectors.representation I (productAction A R)
          (padProductGL (fun i => n i + 1) (fun i => Nat.succ_le_succ (hm i)) u.val) w) = T w

set_option maxHeartbeats 650000 in
theorem realPaddedWhittakerProduct : RealPaddedWhittakerProductStatement n E R := by
  intro hR a L hL
  obtain ⟨T, hT⟩ := smoothProjectiveProductFunctional A E R hR L
  have hCov (g : U) (hg : ∀ i, unitProjection A i g ∈ N (n i)) (w : D) :
      T (DerivativeSmoothVectors.representation I (productAction A R) g w) =
        (∏ i, realWhittakerCharacter (oppositeScale a i) (unitProjection A i g)) * T w := by
    let z := ∏ i, realWhittakerCharacter (oppositeScale a i) (unitProjection A i g)
    let S := T.comp (SmoothAction.derivativeAction I (productAction A R) g)
    have he : S = z • T := by
      apply clm_eq_of_eq_on_pure n E R hR
      intro v
      change T (DerivativeSmoothVectors.representation I (productAction A R) g (pureSmooth A R v)) =
        z * T (pureSmooth A R v)
      rw [representation_pureSmooth, hT, hT, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => hL i ⟨unitProjection A i g, hg i⟩ (v i)
    exact congrArg (fun P : D →L[ℂ] ℂ => P w) he
  refine ⟨T, hT, hCov, fun m hm u w => ?_⟩
  let b := padProductGL (fun i => n i + 1) (fun i => Nat.succ_le_succ (hm i)) u.val
  have hb (i : Fin 2) : unitProjection A i b = padGL (Nat.succ_le_succ (hm i)) u.val := by
    apply Units.ext
    rfl
  have hu (i : Fin 2) : unitProjection A i b ∈ N (n i) := by
    rw [hb]
    exact RealUnequalConvergence.padGL_mem_upperUnipotent _ u.property
  have hχ (i : Fin 2) : realWhittakerCharacter (oppositeScale a i) (unitProjection A i b) =
      realWhittakerCharacter (oppositeScale a i) u.val := by
    rw [hb i]
    exact realWhittakerCharacter_pad_of_le (hm i) (oppositeScale a i) u.val
  have he : (∏ i, realWhittakerCharacter (oppositeScale a i) (unitProjection A i b)) = 1 := by
    calc
      _ = ∏ i, realWhittakerCharacter (oppositeScale a i) u.val :=
        Finset.prod_congr rfl fun i _ => hχ i
      _ = 1 := by
        rw [Fin.prod_univ_two]
        have h₁ : (1 : Fin 2) ≠ 0 := by decide
        simpa [oppositeScale, h₁] using
          RealEqualConvergence.realWhittakerCharacter_mul_neg a u.val
  change T (DerivativeSmoothVectors.representation I (productAction A R) b w) = _
  rw [hCov b hu, he, one_mul]

end Langlands.Global.RankinSelbergGlobal.RealPaddedWhittakerProduct

namespace Langlands.Global.RankinSelbergGlobal.RealPaddedWhittakerProduct

variable (n : Fin 2 → ℕ) (E : Fin 2 → Type*)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  (R : ∀ i, Langlands.GeneralLinear ((n i) + 1) ℝ →* (E i →L[ℂ] E i))

/-- The assertion for representations on complex Banach spaces. -/
def RealPaddedWhittakerProductBanachStatement [∀ i, CompleteSpace (E i)] : Prop :=
  RealPaddedWhittakerProductStatement n E R

theorem realPaddedWhittakerProductBanach [∀ i, CompleteSpace (E i)] : RealPaddedWhittakerProductBanachStatement n E R :=
  realPaddedWhittakerProduct n E R

end Langlands.Global.RankinSelbergGlobal.RealPaddedWhittakerProduct
