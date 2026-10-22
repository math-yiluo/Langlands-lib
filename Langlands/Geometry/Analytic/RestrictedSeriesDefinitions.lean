import Langlands.Geometry.Analytic.TateSeries.Definitions
import Mathlib.RingTheory.PowerSeries.Restricted
import Mathlib.RingTheory.PowerSeries.Trunc

/-! # Polynomial inclusion and distinguished restricted series -/

noncomputable section

universe u

namespace Langlands.Analytic.RestrictedSeries

open Filter
open scoped Topology

variable (A : Type u) [NormedCommRing A] [IsUltrametricDist A]

/-- The one-variable restricted-series algebra with its genuine Gauss norm. -/
abbrev Algebra := StrictTateAlgebra Unit A

/-- The ordinary natural-number coefficient of a restricted series. -/
def coeff (n : ℕ) : Algebra A →L[A] A :=
  StrictTateAlgebra.coefficientCLM Unit A (Finsupp.single () n)

@[simp]
theorem coeff_apply (n : ℕ) (f : Algebra A) :
    coeff A n f = PowerSeries.coeff n f.val := rfl

/-- The actual polynomial inclusion, with restriction verified from finite
support rather than imposed as an additional hypothesis. -/
def ofPolynomial : Polynomial A →ₐ[A] Algebra A where
  toFun p := ⟨p.toPowerSeries, by
    apply (PowerSeries.isRestricted_iff' 1 p.toPowerSeries).mpr
    apply Tendsto.congr' _ (tendsto_const_nhds (x := (0 : ℝ)))
    filter_upwards [eventually_gt_atTop p.natDegree] with n hn
    simp [Polynomial.coeff_eq_zero_of_natDegree_lt hn]⟩
  map_zero' := Subtype.ext Polynomial.coe_zero
  map_one' := Subtype.ext Polynomial.coe_one
  map_add' p q := Subtype.ext (Polynomial.coe_add p q)
  map_mul' p q := Subtype.ext (Polynomial.coe_mul p q)
  commutes' a := Subtype.ext (Polynomial.coe_C a)

variable {A}

/-- A normalized distinguished series has coefficient one in degree `d`,
all coefficients in the unit ball, and strictly smaller coefficients above
that degree. This is a condition on the constructed series, not division data. -/
def IsNormalizedDistinguished (f : Algebra A) (d : ℕ) : Prop :=
  coeff A d f = 1 ∧ (∀ n, ‖coeff A n f‖ ≤ 1) ∧
    ∀ n, d < n → ‖coeff A n f‖ < 1

/-- A distinguished series has an actual invertible coefficient at its last
degree of maximal coefficient norm. No division or factorization is input. -/
def IsDistinguished (f : Algebra A) (d : ℕ) : Prop :=
  IsUnit (coeff A d f) ∧
  (∀ n, ‖coeff A n f‖ ≤ ‖coeff A d f‖) ∧
  ∀ n, d < n → ‖coeff A n f‖ < ‖coeff A d f‖

end Langlands.Analytic.RestrictedSeries
