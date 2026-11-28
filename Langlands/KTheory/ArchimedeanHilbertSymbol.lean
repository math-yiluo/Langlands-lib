import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Basic.Complex.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Archimedean Hilbert symbols

Moore, `moore-1968-group-extensions` (SHA-256
`dfd467339cc20e6eb9bd5d3fbdb06ea2fea8efebdeb479ccaaa4a12529a740d4`), §3,
p. 170 and Theorem 3.2, pp. 171–172. The real quadratic symbol sends the
negative-pair indicator modulo two to `{1, -1}`. The complex symbol is trivial.
-/

noncomputable section

namespace Langlands.KTheory

/-- A positive order admits a primitive real root of unity exactly when it is `1` or `2`. -/
theorem exists_isPrimitiveRoot_real_iff (n : ℕ) (hn : 0 < n) :
    (∃ ζ : ℝ, IsPrimitiveRoot ζ n) ↔ n = 1 ∨ n = 2 := by
  constructor
  · rintro ⟨ζ, hζ⟩
    rcases (pow_eq_one_iff_of_ne_zero hn.ne').mp hζ.pow_eq_one with rfl | ⟨rfl, _⟩
    · exact Or.inl (IsPrimitiveRoot.one_left_iff.mp hζ)
    · exact Or.inr (hζ.unique (IsPrimitiveRoot.neg_one 0 (by decide)))
  · rintro (rfl | rfl)
    · exact ⟨1, IsPrimitiveRoot.one⟩
    · exact ⟨-1, IsPrimitiveRoot.neg_one 0 (by decide)⟩

/-- The element `-1` in the group of quadratic real roots of unity. -/
def realQuadraticNegOne : rootsOfUnity 2 ℝ :=
  rootsOfUnity.mkOfPowEq (-1 : ℝ) (by simp)

@[simp]
theorem coe_realQuadraticNegOne : ((realQuadraticNegOne : ℝˣ) : ℝ) = -1 :=
  rfl

private theorem realQuadraticNegOne_sq : realQuadraticNegOne ^ 2 = 1 :=
  Subtype.ext realQuadraticNegOne.property

private theorem realQuadraticNegOne_ne_one : realQuadraticNegOne ≠ 1 := by
  intro h
  have hlt : (-1 : ℝ) < 1 := (neg_lt_zero.mpr zero_lt_one).trans zero_lt_one
  exact hlt.ne (congrArg (fun z : rootsOfUnity 2 ℝ ↦ (z.val : ℝ)) h)

private def realQuadraticHilbertSymbolRight (a : ℝˣ) : ℝˣ →* rootsOfUnity 2 ℝ where
  toFun b := if (a : ℝ) < 0 ∧ (b : ℝ) < 0 then realQuadraticNegOne else 1
  map_one' := by simp
  map_mul' b c := by
    by_cases ha : (a : ℝ) < 0
    · rcases lt_or_gt_of_ne b.ne_zero with hb | hb <;>
        rcases lt_or_gt_of_ne c.ne_zero with hc | hc
      · simp [ha, hb, hc, (mul_pos_of_neg_of_neg hb hc).not_gt, ← pow_two,
          realQuadraticNegOne_sq]
      · simp [ha, hb, hc.not_gt, mul_neg_of_neg_of_pos hb hc]
      · simp [ha, hb.not_gt, hc, mul_neg_of_pos_of_neg hb hc]
      · simp [ha, hb.not_gt, hc.not_gt, (mul_pos hb hc).not_gt]
    · simp [ha]

/-- The real quadratic Hilbert pairing. Its value is `-1` on pairs of negative units
and `1` on all other pairs. -/
def realQuadraticHilbertSymbol : ℝˣ →* ℝˣ →* rootsOfUnity 2 ℝ :=
  MonoidHom.mk' realQuadraticHilbertSymbolRight <| by
    intro a b
    ext1 c
    change realQuadraticHilbertSymbolRight (a * b) c =
      realQuadraticHilbertSymbolRight a c * realQuadraticHilbertSymbolRight b c
    have comm (x y : ℝˣ) :
        realQuadraticHilbertSymbolRight x y = realQuadraticHilbertSymbolRight y x := by
      simp [realQuadraticHilbertSymbolRight, and_comm]
    rw [comm (a * b) c, map_mul, comm c a, comm c b]

theorem realQuadraticHilbertSymbol_apply (a b : ℝˣ) :
    realQuadraticHilbertSymbol a b =
      if (a : ℝ) < 0 ∧ (b : ℝ) < 0 then realQuadraticNegOne else 1 :=
  rfl

theorem realQuadraticHilbertSymbol_coe (a b : ℝˣ) :
    ((realQuadraticHilbertSymbol a b : ℝˣ) : ℝ) =
      if (a : ℝ) < 0 ∧ (b : ℝ) < 0 then -1 else 1 := by
  rw [realQuadraticHilbertSymbol_apply]
  split <;> rfl

theorem realQuadraticHilbertSymbol_eq_neg_one_iff (a b : ℝˣ) :
    realQuadraticHilbertSymbol a b = realQuadraticNegOne ↔ (a : ℝ) < 0 ∧ (b : ℝ) < 0 := by
  rw [realQuadraticHilbertSymbol_apply]
  split <;> simp_all [Ne.symm realQuadraticNegOne_ne_one]

theorem realQuadraticHilbertSymbol_eq_one_iff (a b : ℝˣ) :
    realQuadraticHilbertSymbol a b = 1 ↔ ¬ ((a : ℝ) < 0 ∧ (b : ℝ) < 0) := by
  rw [realQuadraticHilbertSymbol_apply]
  split <;> simp_all [realQuadraticNegOne_ne_one]

/-- The order-one real Hilbert pairing. -/
def realOrderOneHilbertSymbol : ℝˣ →* ℝˣ →* rootsOfUnity 1 ℝ :=
  1

@[simp]
theorem realOrderOneHilbertSymbol_apply (a b : ℝˣ) :
    realOrderOneHilbertSymbol a b = 1 :=
  rfl

/-- The real Hilbert pairing at an eligible order, with values in the roots of unity of
that order. -/
def realHilbertSymbol (n : ℕ) (hn : n = 1 ∨ n = 2) :
    ℝˣ →* ℝˣ →* rootsOfUnity n ℝ :=
  if h : n = 2 then h.symm ▸ realQuadraticHilbertSymbol
  else (hn.resolve_right h).symm ▸ realOrderOneHilbertSymbol

@[simp]
theorem realHilbertSymbol_one (h : 1 = 1 ∨ 1 = 2) :
    realHilbertSymbol 1 h = realOrderOneHilbertSymbol := by
  simp [realHilbertSymbol]

@[simp]
theorem realHilbertSymbol_two (h : 2 = 1 ∨ 2 = 2) :
    realHilbertSymbol 2 h = realQuadraticHilbertSymbol := by
  simp [realHilbertSymbol]

theorem realHilbertSymbol_coe (n : ℕ) (hn : n = 1 ∨ n = 2) (a b : ℝˣ) :
    ((realHilbertSymbol n hn a b : ℝˣ) : ℝ) =
      if n = 2 ∧ (a : ℝ) < 0 ∧ (b : ℝ) < 0 then -1 else 1 := by
  rcases hn with rfl | rfl <;> simp [realQuadraticHilbertSymbol_coe]

/-- The complex Hilbert pairing of positive order `n`, with constant value `1`. -/
def complexHilbertSymbol (n : ℕ) [NeZero n] :
    ℂˣ →* ℂˣ →* rootsOfUnity n ℂ :=
  1

@[simp]
theorem complexHilbertSymbol_apply (n : ℕ) [NeZero n] (a b : ℂˣ) :
    complexHilbertSymbol n a b = 1 :=
  rfl

end Langlands.KTheory
