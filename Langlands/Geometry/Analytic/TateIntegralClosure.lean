import Langlands.Geometry.Analytic.TateFactorial
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-! # Integral closedness and actual minimal polynomials over a Tate algebra -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTateAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The proved unique factorization property gives integral closedness
through Mathlib's rational-root theorem. -/
theorem isIntegrallyClosed_tate (n : ℕ) :
    IsIntegrallyClosed (StrictTateAlgebra (Fin n) K) := inferInstance

variable (n : ℕ) {B : Type v} [CommRing B]
  [Algebra (StrictTateAlgebra (Fin n) K) B]
  [Module.Finite (StrictTateAlgebra (Fin n) K) B]

omit [CompleteSpace K] in
/-- Finite-module structure constructs the actual integral relation:
the standard minimal polynomial is monic and annihilates the element. -/
theorem minpoly_monic_aeval (b : B) :
    (minpoly (StrictTateAlgebra (Fin n) K) b).Monic ∧
      Polynomial.aeval b (minpoly (StrictTateAlgebra (Fin n) K) b) = 0 :=
  ⟨minpoly.monic (IsIntegral.of_finite _ b), minpoly.aeval _ b⟩

variable [IsDomain B] [Module.IsTorsionFree (StrictTateAlgebra (Fin n) K) B]

/-- Integral closedness proves that the constructed polynomial generates
the actual evaluation kernel in the domain case. -/
theorem minpoly_eval_ker (b : B) :
    RingHom.ker (Polynomial.aeval b :
      Polynomial (StrictTateAlgebra (Fin n) K) →ₐ[StrictTateAlgebra (Fin n) K] B).toRingHom =
      Ideal.span {minpoly (StrictTateAlgebra (Fin n) K) b} :=
  minpoly.ker_eval (IsIntegral.of_finite _ b)

/-- The relation is the actual minimal polynomial over the fraction field,
not just an arbitrary annihilating polynomial. The fraction-field scalar
map is constructed by the localization universal property. -/
theorem minpoly_fractionRing_eq (b : B) :
    let _ : Algebra (FractionRing (StrictTateAlgebra (Fin n) K)) (FractionRing B) :=
      FractionRing.liftAlgebra _ _;
    minpoly (FractionRing (StrictTateAlgebra (Fin n) K)) (algebraMap B (FractionRing B) b) =
      (minpoly (StrictTateAlgebra (Fin n) K) b).map
        (algebraMap (StrictTateAlgebra (Fin n) K)
          (FractionRing (StrictTateAlgebra (Fin n) K))) := by
  let : Algebra (FractionRing (StrictTateAlgebra (Fin n) K)) (FractionRing B) :=
    FractionRing.liftAlgebra _ _
  exact minpoly.isIntegrallyClosed_eq_field_fractions _ _
    (IsIntegral.of_finite (StrictTateAlgebra (Fin n) K) b)

end Langlands.Analytic.StrictTateAlgebra
