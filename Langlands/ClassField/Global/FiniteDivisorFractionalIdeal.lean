import Langlands.ClassField.Global.IdeleDivisor
import Mathlib.RingTheory.DedekindDomain.Factorization

/-! # Finite divisors and nonzero fractional ideals -/

noncomputable section

universe u

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField nonZeroDivisors

variable (E : Type u) [Field E] [NumberField E]

/-- The finite divisor of a nonzero fractional ideal. -/
def fractionalIdealDivisor (I : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FinitePlaceDivisor E :=
  Finsupp.ofSupportFinite (fun w => FractionalIdeal.count E w (I : FractionalIdeal (𝓞 E)⁰ E))
    (Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors (I : FractionalIdeal (𝓞 E)⁰ E)))

@[simp] theorem fractionalIdealDivisor_apply (I : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (w : HeightOneSpectrum (𝓞 E)) :
    fractionalIdealDivisor E I w = FractionalIdeal.count E w (I : FractionalIdeal (𝓞 E)⁰ E) := rfl

/-- Prime multiplicities distinguish nonzero fractional ideals. -/
theorem fractionalIdealDivisor_injective : Function.Injective (fractionalIdealDivisor E) := by
  intro I J h
  apply Units.ext
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' E (Units.ne_zero I),
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' E (Units.ne_zero J)]
  apply finprod_congr
  intro w
  exact congrArg (fun n : ℤ => (w.asIdeal : FractionalIdeal (𝓞 E)⁰ E) ^ n)
    (congrArg (fun d : FinitePlaceDivisor E => d w) h)

/-- The product of prime fractional ideals prescribed by a finite integer divisor. -/
def finiteDivisorFractionalIdeal (d : FinitePlaceDivisor E) : (FractionalIdeal (𝓞 E)⁰ E)ˣ :=
  Units.mk0 (d.prod (fun w n => (w.asIdeal : FractionalIdeal (𝓞 E)⁰ E) ^ n))
    (Finsupp.prod_ne_zero_iff.mpr fun w _ =>
      zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot))

@[simp] theorem finiteDivisorFractionalIdeal_val (d : FinitePlaceDivisor E) :
    (finiteDivisorFractionalIdeal E d : FractionalIdeal (𝓞 E)⁰ E) =
      d.prod (fun w n => (w.asIdeal : FractionalIdeal (𝓞 E)⁰ E) ^ n) := rfl

@[simp] theorem fractionalIdealDivisor_finiteDivisorFractionalIdeal (d : FinitePlaceDivisor E) :
    fractionalIdealDivisor E (finiteDivisorFractionalIdeal E d) = d := by
  ext w
  exact FractionalIdeal.count_finsuppProd E w d

@[simp] theorem finiteDivisorFractionalIdeal_fractionalIdealDivisor
    (I : (FractionalIdeal (𝓞 E)⁰ E)ˣ) :
    finiteDivisorFractionalIdeal E (fractionalIdealDivisor E I) = I := by
  apply fractionalIdealDivisor_injective E
  exact fractionalIdealDivisor_finiteDivisorFractionalIdeal E _

@[simp] theorem fractionalIdealDivisor_one : fractionalIdealDivisor E 1 = 0 := by
  ext w
  exact FractionalIdeal.count_one E w

@[simp] theorem fractionalIdealDivisor_mul (I J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) :
    fractionalIdealDivisor E (I * J) = fractionalIdealDivisor E I + fractionalIdealDivisor E J := by
  ext w
  exact FractionalIdeal.count_mul E w (Units.ne_zero I) (Units.ne_zero J)

@[simp] theorem finiteDivisorFractionalIdeal_zero : finiteDivisorFractionalIdeal E 0 = 1 := by
  apply fractionalIdealDivisor_injective E
  simp

@[simp] theorem finiteDivisorFractionalIdeal_add (d e : FinitePlaceDivisor E) :
    finiteDivisorFractionalIdeal E (d + e) =
      finiteDivisorFractionalIdeal E d * finiteDivisorFractionalIdeal E e := by
  apply fractionalIdealDivisor_injective E
  simp

/-- The canonical prime-product equivalence between finite divisors and nonzero fractional ideals. -/
def finiteDivisorFractionalIdealEquiv :
    Multiplicative (FinitePlaceDivisor E) ≃* (FractionalIdeal (𝓞 E)⁰ E)ˣ where
  toFun d := finiteDivisorFractionalIdeal E d.toAdd
  invFun I := Multiplicative.ofAdd (fractionalIdealDivisor E I)
  left_inv d := fractionalIdealDivisor_finiteDivisorFractionalIdeal E d.toAdd
  right_inv := finiteDivisorFractionalIdeal_fractionalIdealDivisor E
  map_mul' d e := finiteDivisorFractionalIdeal_add E d.toAdd e.toAdd

@[simp] theorem finiteDivisorFractionalIdealEquiv_apply (d : FinitePlaceDivisor E) :
    (finiteDivisorFractionalIdealEquiv E (Multiplicative.ofAdd d) : FractionalIdeal (𝓞 E)⁰ E) =
      d.prod (fun w n => (w.asIdeal : FractionalIdeal (𝓞 E)⁰ E) ^ n) := rfl

@[simp] theorem finiteDivisorFractionalIdealEquiv_symm_apply
    (I : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (w : HeightOneSpectrum (𝓞 E)) :
    ((finiteDivisorFractionalIdealEquiv E).symm I).toAdd w =
      FractionalIdeal.count E w (I : FractionalIdeal (𝓞 E)⁰ E) := rfl

@[simp] theorem finiteDivisorFractionalIdeal_single (w : HeightOneSpectrum (𝓞 E)) (n : ℤ) :
    (finiteDivisorFractionalIdeal E (Finsupp.single w n) : FractionalIdeal (𝓞 E)⁰ E) =
      (w.asIdeal : FractionalIdeal (𝓞 E)⁰ E) ^ n := by
  rw [finiteDivisorFractionalIdeal_val, Finsupp.prod_single_index (zpow_zero _)]

end Langlands.ClassField.Global
