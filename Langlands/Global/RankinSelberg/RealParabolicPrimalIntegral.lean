import Langlands.Global.RankinSelberg.ArchimedeanIntegrals
import Langlands.Global.RankinSelberg.ArchimedeanRealPairFactor
import Langlands.Global.RankinSelberg.OrdinaryNormalizationUniqueness
import Langlands.Global.RankinSelberg.UnequalAnalyticMatrices

/-! # Primal real Rankin–Selberg kernels under a parabolic restriction -/

noncomputable section

open Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open MeasureTheory
open scoped SchwartzMap Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealParabolicPrimalIntegral

open ArchimedeanLocal
open Langlands.RankinSelberg (LeftUnipotentQuotient)

local notation "G" => fun r => Langlands.GeneralLinear (r + 1) ℝ
local notation "Row" => fun r : ℕ => Fin (r + 1) → ℝ
local notation "Q" => fun r => LeftUnipotentQuotient r ℝ
local notation "P" => ArchimedeanLocal.detPower realNormalizedAbs

/-- The coefficient restriction given by a leading-block parabolic lift. -/
def HasLeadingBlockRestriction {r u : ℕ} (h : u < r)
    (W : G r → ℂ) (U : G u → ℂ) (Φ : 𝓢(Row u, ℂ)) : Prop :=
  ∀ g, W (padGL (Nat.succ_le_succ h.le) g) =
    U g * Φ (Langlands.RankinSelberg.lastRow g) * P g (((r - u : ℕ) : ℂ) / 2)

/-- The kernel on the group of rank `t+1` obtained by restricting both Whittaker
functions to the leading block of that rank. -/
def realLoweredPairKernel {r u t : ℕ} (hr : t < r) (hu : t < u)
    (W : G r → ℂ) (V : G u → ℂ) (s : ℂ) (q : Q t) : ℂ :=
  let g := q.out
  W (padGL (Nat.succ_le_succ hr.le) g) * V (padGL (Nat.succ_le_succ hu.le) g) *
    P g (s - (((r - t : ℕ) : ℂ) + ((u - t : ℕ) : ℂ)) / 2)

private theorem detPower_add {n : ℕ} (g : G n) (s z : ℂ) :
    P g (s + z) = P g s * P g z := by
  rw [ArchimedeanLocal.detPower, add_mul, Complex.exp_add]
  rfl

private theorem detPower_pad {r u : ℕ} (h : u < r) (g : G u) (s : ℂ) :
    P (padGL (Nat.succ_le_succ h.le) g) s = P g s := by
  unfold ArchimedeanLocal.detPower
  rw [UnequalAnalytic.det_padGL]

private theorem lastRow_pad {r u : ℕ} (h : u < r) (g : G u) :
    Langlands.RankinSelberg.lastRow (padGL (Nat.succ_le_succ h.le) g) = Pi.single (Fin.last r) 1 := by
  funext j
  change (padGL (Nat.succ_le_succ h.le) g).val (Fin.last r) j = _
  rw [UnequalAnalytic.padGL_row _ _ _ (show u + 1 ≤ (Fin.last r : ℕ) from h)]
  by_cases hj : j = Fin.last r
  · subst j
    rw [Matrix.one_apply_eq, Pi.single_eq_same]
  · rw [Matrix.one_apply_ne (fun he => hj he.symm), Pi.single_eq_of_ne hj]

private theorem unequal_of_equal {r u : ℕ} (h : u < r) (W : G r → ℂ) (U V : G u → ℂ)
    (Φ : 𝓢(Row u, ℂ)) (hW : HasLeadingBlockRestriction h W U Φ) (s : ℂ) :
    realUnequalIntegrand h W V s = realEqualIntegrand U V Φ s := by
  funext q
  let g := q.out
  let b : ℂ := ((r - u : ℕ) : ℂ) / 2
  change W (padGL (Nat.succ_le_succ h.le) g) * V g * P g (s - b) =
    U g * V g * Φ (Langlands.RankinSelberg.lastRow g) * P g s
  rw [hW g, show P g s = P g b * P g (s - b) from by rw [← detPower_add]; ring_nf]
  ring

private theorem unequal_of_unequal {r u t : ℕ} (h : u < r) (ht : t < u)
    (W : G r → ℂ) (U : G u → ℂ) (V : G t → ℂ) (Φ : 𝓢(Row u, ℂ))
    (hW : HasLeadingBlockRestriction h W U Φ) (hΦ : Φ (Pi.single (Fin.last u) 1) = 1)
    (s : ℂ) : realUnequalIntegrand (ht.trans h) W V s = realUnequalIntegrand ht U V s := by
  funext q
  let g := q.out
  let b : ℂ := ((r - u : ℕ) : ℂ) / 2
  let c : ℂ := ((r - t : ℕ) : ℂ) / 2
  let d : ℂ := ((u - t : ℕ) : ℂ) / 2
  change W (padGL (Nat.succ_le_succ (ht.trans h).le) g) * V g * P g (s - c) =
    U (padGL (Nat.succ_le_succ ht.le) g) * V g * P g (s - d)
  rw [← UnequalAnalytic.padGL_padGL (Nat.succ_le_succ ht.le) (Nat.succ_le_succ h.le),
    hW, lastRow_pad ht, hΦ, mul_one, detPower_pad ht]
  have hsub : (r - t : ℕ) = (r - u : ℕ) + (u - t : ℕ) := by omega
  have hpow : P g (s - d) = P g b * P g (s - c) := by
    rw [← detPower_add]
    congr 1
    simp only [b, c, d, hsub, Nat.cast_add]
    ring
  rw [hpow]
  ring

private theorem lowered_of_weighted_unequal {r u t : ℕ} (hr : t < r) (hu : t < u)
    (W : G r → ℂ) (U : G t → ℂ) (V : G u → ℂ) (Φ : 𝓢(Row t, ℂ))
    (hW : HasLeadingBlockRestriction hr W U Φ) (s : ℂ) :
    realLoweredPairKernel hr hu W V s =
      fun q => realUnequalIntegrand hu V U s q * Φ (Langlands.RankinSelberg.lastRow q.out) := by
  funext q
  let g := q.out
  let b : ℂ := ((r - t : ℕ) : ℂ) / 2
  let d : ℂ := ((u - t : ℕ) : ℂ) / 2
  change W (padGL (Nat.succ_le_succ hr.le) g) * V (padGL (Nat.succ_le_succ hu.le) g) *
    P g (s - (((r - t : ℕ) : ℂ) + ((u - t : ℕ) : ℂ)) / 2) =
      (V (padGL (Nat.succ_le_succ hu.le) g) * U g * P g (s - d)) * Φ (Langlands.RankinSelberg.lastRow g)
  rw [hW g, show P g (s - d) =
    P g b * P g (s - (((r - t : ℕ) : ℂ) + ((u - t : ℕ) : ℂ)) / 2) from by
      rw [← detPower_add]
      congr 1
      dsimp [b, d]
      ring]
  ring

/-- Given the leading-block coefficient restriction, the primal kernel reduces
according to the relative ranks of the leading block and the other group. -/
def RealParabolicPrimalIntegralStatement : Prop :=
  (∀ (r u : ℕ) (h : u < r) (W : G r → ℂ) (U V : G u → ℂ) (Φ : 𝓢(Row u, ℂ)),
    HasLeadingBlockRestriction h W U Φ →
    ∀ s : ℂ, realUnequalIntegrand h W V s = realEqualIntegrand U V Φ s) ∧
  (∀ (r u t : ℕ) (h : u < r) (ht : t < u) (W : G r → ℂ) (U : G u → ℂ)
    (V : G t → ℂ) (Φ : 𝓢(Row u, ℂ)), HasLeadingBlockRestriction h W U Φ →
    Φ (Pi.single (Fin.last u) 1) = 1 →
    ∀ s : ℂ, realUnequalIntegrand (ht.trans h) W V s = realUnequalIntegrand ht U V s) ∧
  (∀ (r u t : ℕ) (hr : t < r) (hu : t < u) (W : G r → ℂ) (U : G t → ℂ)
    (V : G u → ℂ) (Φ : 𝓢(Row t, ℂ)), HasLeadingBlockRestriction hr W U Φ →
    ∀ s : ℂ, realLoweredPairKernel hr hu W V s =
      fun q => realUnequalIntegrand hu V U s q * Φ (Langlands.RankinSelberg.lastRow q.out))

theorem realParabolicPrimalIntegral : RealParabolicPrimalIntegralStatement :=
  ⟨fun _ _ => unequal_of_equal, fun _ _ _ => unequal_of_unequal,
    fun _ _ _ => lowered_of_weighted_unequal⟩

/-- An identity with the leading-block integral transfers its entire normalization
by multiplication with the complementary pair denominator. -/
def appendLeftNormalization (ds es fs : List RealBlock) (I J : ℂ → ℂ) (h : I = J)
    (N : OrdinaryIntegralNormalization I (fun s => ((realPairLFactor ds fs).denominator s)⁻¹)) :
    OrdinaryIntegralNormalization J (fun s => ((realPairLFactor (ds ++ es) fs).denominator s)⁻¹) := by
  let den := (realPairLFactor es fs).denominator
  refine ⟨fun s => den s * N.value s, fun s hs => ?_, ?_⟩
  · exact ((realPairLFactor es fs).entire.analyticAt s).mul (N.analytic s hs)
  obtain ⟨b, hb⟩ := N.eq_on_right
  obtain ⟨c, hc⟩ := ArchimedeanRealPairFactor.realLFactor_ne_zero (realPairBlocks es fs)
  refine ⟨max b c, fun s hs => ?_⟩
  have hd : (realPairLFactor (ds ++ es) fs).denominator s =
      (realPairLFactor ds fs).denominator s * den s := by
    simp [realPairLFactor, realPairBlocks, List.flatMap_append, realLFactor_append, ReciprocalEntire.mul, den]
  rw [← h, hb s ((le_max_left _ _).trans_lt hs), hd, mul_inv]
  have he : den s ≠ 0 := hc s ((le_max_right _ _).trans_lt hs)
  field_simp

end Langlands.Global.RankinSelbergGlobal.RealParabolicPrimalIntegral
