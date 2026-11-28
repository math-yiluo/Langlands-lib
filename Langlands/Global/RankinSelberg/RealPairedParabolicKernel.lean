import Langlands.Global.RankinSelberg.RealPairedRankTransfer
import Langlands.Global.RankinSelberg.RealParabolicPrimalIntegral

/-! # Doubly padded kernels of real parabolic lifts -/

noncomputable section

open scoped ContDiff Manifold Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false

namespace Langlands.Global.RankinSelbergGlobal.RealPairedRankRaising

open Langlands.Archimedean Langlands.Archimedean.DerivativeSmoothVectors
open ArchimedeanLocal CompletedProjectiveRepresentation
open RealPaddedExponential RealParabolicPrimalIntegral RealRankRaisingIntegral

local notation "G" => fun n : ℕ => Langlands.GeneralLinear (n + 1) ℝ
local notation "Mat" => fun n : ℕ => Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ
local notation "Row" => fun n : ℕ => Fin (n + 1) → ℝ

variable (n : Fin 2 → ℕ) {E : Fin 2 → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  (R : ∀ i, G (n i) →* (E i →L[ℂ] E i))

local notation "A" => fun i => Mat (n i)
local notation "I" => 𝓘(ℝ, (∀ i : Fin 2, A i))
local notation "D" => DerivativeSmoothVectors I (productAction A R)
local notation "D₀" => fun i => DerivativeSmoothVectors 𝓘(ℝ, A i) (R i)

/-- The half-sum of the two gaps between the ambient ranks and the comparison rank. -/
def pairedDetShift (m : ℕ) : ℂ := (((n 0 - m : ℕ) : ℂ) + ((n 1 - m : ℕ) : ℂ)) / 2

private theorem pairedDetShift_sub {t m : ℕ} (ht : t ≤ m) (hm : ∀ i, m ≤ n i) (s : ℂ) :
    s - pairedDetShift n m - (m - t : ℕ) = s - pairedDetShift n t := by
  have h (i : Fin 2) : n i - t = (n i - m) + (m - t) := by have := hm i; omega
  simp only [pairedDetShift, h 0, h 1, Nat.cast_add]
  ring

/-- The coefficient in one slot of a pure smooth pair. -/
def slotCoefficient (L : ∀ i, D₀ i →L[ℂ] ℂ) (v : ∀ i, D₀ i) (i : Fin 2) (g : G (n i)) : ℂ :=
  L i (representation 𝓘(ℝ, A i) (R i) g (v i))

/-- On pure smooth tensors, the paired coefficient on the smaller quotient is the product of
both individual coefficients at the leading-block embeddings. -/
theorem paddedPairCoefficient_pure (L : ∀ i, D₀ i →L[ℂ] ℂ) (T : D →L[ℂ] ℂ)
    (hT : ∀ v : ∀ i, D₀ i, T (pureSmooth A R v) = ∏ i, L i (v i))
    (t : ℕ) (ht : ∀ i, t ≤ n i) (v : ∀ i, D₀ i) (q : Langlands.RankinSelberg.LeftUnipotentQuotient t ℝ) :
    paddedPairCoefficient n E R t ht T (pureSmooth A R v) q =
      ∏ i, slotCoefficient n R L v i (padGL (Nat.succ_le_succ (ht i)) q.out) := by
  let g := padProductGL (fun i => n i + 1) (fun i => Nat.succ_le_succ (ht i)) q.out
  have hg (i : Fin 2) : unitProjection A i g = padGL (Nat.succ_le_succ (ht i)) q.out := Units.ext rfl
  unfold paddedPairCoefficient
  change T (representation I (productAction A R) g (pureSmooth A R v)) = _
  rw [representation_pureSmooth, hT]
  simp only [hg, slotCoefficient]

/-- The product over the two distinct slots may be taken in their specified order. -/
theorem prod_eq_mul_of_ne {M : Type*} [CommMonoid M] (i j : Fin 2) (h : i ≠ j) (f : Fin 2 → M) :
    ∏ k, f k = f i * f j := by
  rw [Fin.prod_univ_two]
  fin_cases i <;> fin_cases j <;> simp_all [mul_comm]

/-- At a strict cut in either slot, the paired kernel is the ordinary lower unequal kernel
with the row profile and with the uncut group first. -/
theorem pairedParabolicKernel_of_leading (i j : Fin 2) (hij : i ≠ j)
    (L : ∀ k, D₀ k →L[ℂ] ℂ) (T : D →L[ℂ] ℂ)
    (hT : ∀ v : ∀ k, D₀ k, T (pureSmooth A R v) = ∏ k, L k (v k))
    (t m : ℕ) (ht : t < m) (hm : ∀ k, m ≤ n k)
    (v : ∀ k, D₀ k) (U : G t → ℂ) (Φ : 𝓢(Row t, ℂ))
    (hW : HasLeadingBlockRestriction (ht.trans_le (hm i)) (slotCoefficient n R L v i) U Φ)
    (s : ℂ) :
    paddedPairKernel n E R t (fun k => ht.le.trans (hm k)) T (pureSmooth A R v, none)
        (s - pairedDetShift n m - (m - t : ℕ)) =
      fun q => realUnequalIntegrand (ht.trans_le (hm j)) (slotCoefficient n R L v j) U s q *
        Φ (Langlands.RankinSelberg.lastRow q.out) := by
  let hr := ht.trans_le (hm i)
  let hu := ht.trans_le (hm j)
  let W := slotCoefficient n R L v i
  let V := slotCoefficient n R L v j
  rw [paddedPairKernel_none, pairedDetShift_sub n ht.le hm, ← realParabolicPrimalIntegral.2.2
    (n i) (n j) t hr hu W U V Φ hW s]
  funext q
  rw [paddedPairCoefficient_pure n R L T hT, prod_eq_mul_of_ne i j hij]
  have hShift : pairedDetShift n t = (((n i - t : ℕ) : ℂ) + ((n j - t : ℕ) : ℂ)) / 2 := by
    have he := prod_eq_mul_of_ne (M := Multiplicative ℂ) i j hij
      (fun k => Multiplicative.ofAdd (((n k - t : ℕ) : ℂ)))
    rw [Fin.prod_univ_two] at he
    exact congrArg (fun z : Multiplicative ℂ => Multiplicative.toAdd z / 2) he
  rw [hShift]
  rfl

/-- At a cut strictly below both ambient ranks, the shifted padded kernel of a leading parabolic
lift is the ordinary lower unequal kernel in the reversed order, with the lifted row profile. -/
def RealPairedParabolicKernelStatement : Prop :=
  ∀ (L : ∀ i, D₀ i →L[ℂ] ℂ) (T : D →L[ℂ] ℂ),
    (∀ v : ∀ i, D₀ i, T (pureSmooth A R v) = ∏ i, L i (v i)) →
    ∀ (t m : ℕ) (ht : t < m) (hm : ∀ i, m ≤ n i)
      (v : ∀ i, D₀ i) (U : G t → ℂ) (Φ : 𝓢(Row t, ℂ)),
      HasLeadingBlockRestriction (ht.trans_le (hm 0)) (slotCoefficient n R L v 0) U Φ →
      ∀ s : ℂ,
        paddedPairKernel n E R t (fun i => ht.le.trans (hm i)) T (pureSmooth A R v, none)
          (s - pairedDetShift n m - (m - t : ℕ)) =
        fun q => realUnequalIntegrand (ht.trans_le (hm 1)) (slotCoefficient n R L v 1) U s q *
          Φ (Langlands.RankinSelberg.lastRow q.out)

theorem realPairedParabolicKernel : RealPairedParabolicKernelStatement n R := by
  intro L T hT t m ht hm v U Φ hW s
  exact pairedParabolicKernel_of_leading n R 0 1 (by decide) L T hT t m ht hm v U Φ hW s

end Langlands.Global.RankinSelbergGlobal.RealPairedRankRaising
