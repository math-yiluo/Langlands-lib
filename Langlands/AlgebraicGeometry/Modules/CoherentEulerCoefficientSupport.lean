import Langlands.AlgebraicGeometry.Modules.CoherentEulerPolynomialAdditivity
import Langlands.AlgebraicGeometry.Modules.CoherentEulerPolynomialZeroDimensional
import Langlands.AlgebraicGeometry.Modules.IntegralIdealOpenProof
import Langlands.AlgebraicGeometry.Picard.LineBundleEulerPolynomial

/-! # Top Euler coefficients and strict support bounds -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.SchemeModule

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {X : Scheme.{u}} {K : Type u} [Field K]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]

/-- The coefficient at a common dimension bound is nonnegative and is positive
exactly when the sheaf does not satisfy the next smaller strict support bound. -/
def EulerCoefficientDetectsSupport (M : X.Modules) [M.IsQuasicoherent]
    (hM : HasFiniteAffineSections M) (L : Picard.LineBundle X) (d : ℕ) : Prop :=
  0 ≤ (coherentEulerPolynomial f M hM L d).coeff d ∧
    (0 < (coherentEulerPolynomial f M hM L d).coeff d ↔
      ¬ HasSupportDimensionLT M d)

variable [IsNoetherian X] [X.IsSeparated]

/-- A strict support bound forces the coefficient at that bound to vanish. -/
theorem coherentEulerPolynomial_coeff_eq_zero_of_supportDimensionLT
    (M : X.Modules) [M.IsQuasicoherent] (hM : HasFiniteAffineSections M)
    (L : Picard.LineBundle X) (d : ℕ) (hS : HasSupportDimensionLT M d) :
    (coherentEulerPolynomial f M hM L d).coeff d = 0 := by
  cases d with
  | zero =>
      rw [coherentEulerPolynomial_zero f M hM L 0 hS.isZero,
        Polynomial.coeff_zero]
  | succ d =>
      rw [coherentEulerPolynomial_eq_of_supportDimensionLT f M hM L (d + 1) d
        (hS.mono (by omega)) hS]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt
        ((coherentEulerPolynomial_natDegree_le f M hM L d).trans_lt (Nat.lt_succ_self d))

omit [X.IsSeparated] in
/-- A sheaf of support dimension at most zero satisfies the coefficient criterion. -/
theorem eulerCoefficientDetectsSupport_zero
    (M : X.Modules) [M.IsQuasicoherent] (hM : HasFiniteAffineSections M)
    (L : Picard.LineBundle X) (hS : HasSupportDimensionLT M 1) :
    EulerCoefficientDetectsSupport f M hM L 0 := by
  have hpos :
      0 < (coherentEulerPolynomial f M hM L 0).coeff 0 ↔ ¬ IsZero M := by
    rw [coherentEulerPolynomial_zero_eq_C f M hM L, coherentEulerConstantPolynomial,
      Polynomial.coeff_C_zero, Int.cast_pos]
    exact coherentEulerCharacteristic_pos_iff_of_supportDimensionLT_one f M hM hS
  constructor
  · by_cases hz : IsZero M
    · rw [coherentEulerPolynomial_zero f M hM L 0 hz, Polynomial.coeff_zero]
    · exact le_of_lt (hpos.mpr hz)
  · simpa only [hasSupportDimensionLT_zero_iff] using hpos

/-- A nonzero integral ideal and the structure module have the same coefficient
at any finite upper bound for the ambient dimension. -/
theorem coherentEulerPolynomial_ideal_coeff_eq_structureModule
    [IsIntegral X] (I : X.Modules) [I.IsQuasicoherent]
    (hI : HasFiniteAffineSections I)
    (ι : I ⟶ structureModule X) [Mono ι] (hne : ¬ IsZero I)
    (L : Picard.LineBundle X) (d : ℕ) (hX : topologicalKrullDim X ≤ d) :
    (coherentEulerPolynomial f I hI L d).coeff d =
      (Picard.lineBundleEulerPolynomial f L d).coeff d := by
  let O := structureModule X
  let : O.IsQuasicoherent := (Picard.LineBundle.trivial X).property.isQuasicoherent
  have hO : HasFiniteAffineSections O := hasFiniteAffineSections_structureSheaf X
  have : (cokernel ι).IsQuasicoherent :=
    QuasicoherentLocal.isQuasicoherent_cokernel ι
  have hQ : HasFiniteAffineSections (cokernel ι) := hO.cokernel ι
  let S := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel ι) }
  have hadd := coherentEulerPolynomial_add f S hS hI hO hQ L d
  have hzero := coherentEulerPolynomial_coeff_eq_zero_of_supportDimensionLT f
    (cokernel ι) hQ L d (hasSupportDimensionLT_cokernel_ideal X I ι hne d hX)
  have hcoeff := congrArg (fun P : Polynomial ℚ => P.coeff d) hadd
  change (Picard.lineBundleEulerPolynomial f L d).coeff d =
    (coherentEulerPolynomial f I hI L d +
      coherentEulerPolynomial f (cokernel ι) hQ L d).coeff d at hcoeff
  rw [Polynomial.coeff_add, hzero, add_zero] at hcoeff
  exact hcoeff.symm

end Langlands.AlgebraicGeometry.Modules.DerivedSections
