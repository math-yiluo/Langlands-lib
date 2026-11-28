import Langlands.Global.RankinSelberg.RealPairedStrictPrimal

/-! # Terminal tests on pure smooth real Whittaker pairs -/

noncomputable section

open Langlands.Archimedean Langlands.Archimedean.DerivativeSmoothVectors
open scoped ContDiff Manifold Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false

namespace Langlands.Global.RankinSelbergGlobal.RealPairedRankRaising

open ArchimedeanLocal CompletedProjectiveRepresentation
open RealRankRaisingIntegral

local notation "G" => fun n : ℕ => Langlands.GeneralLinear (n + 1) ℝ
local notation "Mat" => fun n : ℕ => Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ
local notation "Row" => fun n : ℕ => Fin (n + 1) → ℝ

/-- The two ambient rank indices in their specified order. -/
abbrev pairRanks (r t : ℕ) : Fin 2 → ℕ := Fin.cases r (fun _ => t)

@[simp] theorem pairRanks_zero (r t : ℕ) : pairRanks r t 0 = r := rfl
@[simp] theorem pairRanks_one (r t : ℕ) : pairRanks r t 1 = t := rfl

private theorem padGL_same {r : ℕ} (g : G r) : padGL (le_refl (r + 1)) g = g := by
  apply Units.ext
  ext i j
  rw [UnequalAnalytic.padGL_apply]
  simp only [i.isLt, j.isLt, and_self, dite_true]

variable (r t : ℕ) {E : Fin 2 → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]

local notation "A" => fun i => Mat (pairRanks r t i)
local notation "I" => 𝓘(ℝ, (∀ i : Fin 2, A i))

variable (R : ∀ i, G (pairRanks r t i) →* (E i →L[ℂ] E i))

local notation "D" => DerivativeSmoothVectors I (productAction A R)
local notation "D₀" => fun i => DerivativeSmoothVectors 𝓘(ℝ, A i) (R i)

/-- The ordinary kernels at the smaller terminal rank agree with the usual unequal-rank
kernels on pure smooth tensors, in either order of the ambient factors. -/
def RealPairedUnequalOrdinaryKernelsStatement : Prop :=
  ∀ (L : ∀ i, D₀ i →L[ℂ] ℂ) (T : D →L[ℂ] ℂ),
    (∀ v : ∀ i, D₀ i, T (pureSmooth A R v) = ∏ i, L i (v i)) →
    ∀ v : ∀ i, D₀ i,
      let W₀ := slotCoefficient (pairRanks r t) R L v 0
      let W₁ := slotCoefficient (pairRanks r t) R L v 1
      (∀ (h : t < r) (hm : ∀ i, t ≤ pairRanks r t i) (s : ℂ),
        ordinaryPaddedPairKernel (pairRanks r t) E R t hm T (pureSmooth A R v, none) s =
          realUnequalIntegrand h W₀ W₁ s) ∧
      (∀ (h : r < t) (hm : ∀ i, r ≤ pairRanks r t i) (s : ℂ),
        ordinaryPaddedPairKernel (pairRanks r t) E R r hm T (pureSmooth A R v, none) s =
          realUnequalIntegrand h W₁ W₀ s)

theorem realPairedUnequalOrdinaryKernels : RealPairedUnequalOrdinaryKernelsStatement r t R := by
  intro L T hT v W₀ W₁
  constructor
  · intro h hm s
    unfold ordinaryPaddedPairKernel
    rw [paddedPairKernel_none]
    funext q
    change paddedPairCoefficient (pairRanks r t) E R _ hm T (pureSmooth A R v) q * _ = _
    rw [paddedPairCoefficient_pure _ R L T hT, Fin.prod_univ_two]
    change W₀ (padGL _ q.out) * W₁ (padGL (le_refl (t + 1)) q.out) *
      realQuotientDetPower q (s - pairedDetShift (pairRanks r t) t) = _
    rw [padGL_same]
    simp only [pairedDetShift, pairRanks_zero, pairRanks_one, Nat.sub_self, Nat.cast_zero, add_zero]
    rfl
  · intro h hm s
    unfold ordinaryPaddedPairKernel
    rw [paddedPairKernel_none]
    funext q
    change paddedPairCoefficient (pairRanks r t) E R _ hm T (pureSmooth A R v) q * _ = _
    rw [paddedPairCoefficient_pure _ R L T hT, Fin.prod_univ_two]
    change W₀ (padGL (le_refl (r + 1)) q.out) * W₁ (padGL _ q.out) *
      realQuotientDetPower q (s - pairedDetShift (pairRanks r t) r) = _
    rw [padGL_same, mul_comm (W₀ q.out)]
    simp only [pairedDetShift, pairRanks_zero, pairRanks_one, Nat.sub_self, Nat.cast_zero, zero_add]
    rfl

/-- At equal ranks the terminal pure paired kernel is the ordinary equal-rank kernel with its
Schwartz row test. -/
def RealPairedEqualOrdinaryKernelStatement : Prop :=
  ∀ (R : ∀ i, G (pairRanks r r i) →* (E i →L[ℂ] E i)),
    let B := fun i => Mat (pairRanks r r i)
    let model := 𝓘(ℝ, (∀ i : Fin 2, B i))
    let Joint := DerivativeSmoothVectors model (productAction B R)
    let Separate := fun i => DerivativeSmoothVectors 𝓘(ℝ, B i) (R i)
    ∀ (L : ∀ i, Separate i →L[ℂ] ℂ) (T : Joint →L[ℂ] ℂ),
      (∀ v : ∀ i, Separate i, T (pureSmooth B R v) = ∏ i, L i (v i)) →
      ∀ (v : ∀ i, Separate i) (Φ : 𝓢(Row r, ℂ)) (hm : ∀ i, r ≤ pairRanks r r i) (s : ℂ),
        ordinaryPaddedPairKernel (pairRanks r r) E R r hm T (pureSmooth B R v, some Φ) s =
          realEqualIntegrand (slotCoefficient (pairRanks r r) R L v 0)
            (slotCoefficient (pairRanks r r) R L v 1) Φ s

theorem realPairedEqualOrdinaryKernel : RealPairedEqualOrdinaryKernelStatement r (E := E) := by
  intro R B model Joint Separate L T hT v Φ hm s
  unfold ordinaryPaddedPairKernel
  rw [paddedPairKernel_some]
  funext q
  change paddedPairCoefficient (pairRanks r r) E R r hm T (pureSmooth B R v) q * _ * _ = _
  rw [paddedPairCoefficient_pure _ R L T hT, Fin.prod_univ_two]
  change slotCoefficient (pairRanks r r) R L v 0 (padGL (le_refl (r + 1)) q.out) *
    slotCoefficient (pairRanks r r) R L v 1 (padGL (le_refl (r + 1)) q.out) *
    Φ (Langlands.RankinSelberg.lastRow q.out) * realQuotientDetPower q (s - pairedDetShift (pairRanks r r) r) = _
  simp only [padGL_same, pairedDetShift, pairRanks_zero, pairRanks_one, Nat.sub_self, Nat.cast_zero,
    add_zero, zero_div, sub_zero]
  rfl

/-- Pure paired kernels recover both families of ordinary real quotient kernels. -/
def RealPairedOrdinaryKernelsStatement : Prop :=
  RealPairedUnequalOrdinaryKernelsStatement r t R ∧ RealPairedEqualOrdinaryKernelStatement r (E := E)

theorem realPairedOrdinaryKernels : RealPairedOrdinaryKernelsStatement r t R :=
  ⟨realPairedUnequalOrdinaryKernels r t R, realPairedEqualOrdinaryKernel r⟩

end Langlands.Global.RankinSelbergGlobal.RealPairedRankRaising
