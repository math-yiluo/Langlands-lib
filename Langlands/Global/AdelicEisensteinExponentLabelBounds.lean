import Langlands.Global.AdelicEisensteinUnitaryExponentStatement
import Langlands.Global.AdelicCharacterParameterPullback
import Langlands.Global.AdelicEisensteinImaginaryContinuation
import Langlands.Global.RelativeRootChamberLog
import Langlands.GroupScheme.Rational.ParabolicRootPresentationSimpleRoots

/-! # Norm bounds for affine Eisenstein exponent labels

Lapid 2011, Lemma 6, and Delorme 2023, §2 and §4.1: on the dominant positive split
component, a normalized offset given in real part by a nonpositive combination of positive
roots gives a raw exponent value bounded by the half modulus at imaginary parameters. -/

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct NNReal

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints

variable {F : Type} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)

local notation "Q" => fam.P J
local notation "A" => CommGroupScheme.toGrp (fam.A J)
local notation "ι" => fam.a J ≫ fam.l J

/-- Every positive relative root has nonnegative logarithm on a dominant point of the
positive split component. The simple roots in the Levi index restrict to zero. -/
theorem characterLog_restrict_nonneg_of_isDominantSplitPoint
    {s : PositiveRealTorus.intrinsicSubgroup F (fam.A J)}
    (hs : fam.IsDominantSplitPoint J s) {β : characterLattice fam.T}
    (hβ : β ∈ positiveRelativeRoots fam.i fam.ν) :
    0 ≤ characterLog F A s.val (fam.f J ≫ β) := by
  let logAt : characterLattice (fam.A J) →+ ℝ := characterLog F A s.val
  refine positiveRelativeRoots_induction fam.i fam.ν
    (P := fun α => 0 ≤ logAt (fam.f J ≫ α)) ?_ ?_ hβ
  · intro α hα
    by_cases hJ : α ∈ J.val
    · let r : ParabolicRootPresentation (fam.p J) (fam.l J) (fam.a J) :=
        ⟨⟨fam.T, fam.i, fam.ν, J.val, fam.f J⟩, fam.isCompatible J⟩
      have hzero : fam.f J ≫ α = 0 := r.selectedRoot_restrict_eq_zero hJ
      simp only [hzero, map_zero, le_refl]
    · change 0 ≤ Real.log
        ((PositiveRealTorus.normCharacter F (fam.A J) (fam.f J ≫ α) s : ℝ≥0) : ℝ)
      simpa only [Units.val_one, NNReal.coe_one, Real.log_one] using
        (PositiveRealTorus.log_unit_le_log_unit_iff 1
          (PositiveRealTorus.normCharacter F (fam.A J) (fam.f J ≫ α) s)).mpr (hs α hα hJ)
  · intro α _ beta _ hα hbeta
    rw [Preadditive.comp_add, map_add]
    exact add_nonneg hα hbeta

/-- The norm of a raw exponent is the half modulus times the exponential of the real
normalized pairing, which can be computed entirely on the split component. -/
theorem norm_parameterPower_add_halfModulus_eq
    (mu : ComplexCharacterParameter F Q)
    (s : PositiveRealTorus.intrinsicSubgroup F (fam.A J)) :
    let a := PositiveRealTorus.positivePointMap F Q (fam.A J) ι s
    ‖parameterPower F Q (mu + halfModulusParameter F Q) a‖ =
      Real.exp (realParameterPairing F A (parameterRealPart F A (parameterRestrict ι mu))
        (characterLog F A s.val)) * ‖fam.halfModulus J a‖ := by
  dsimp only
  rw [parameterPower_add, norm_mul]
  change ‖parameterPower F Q mu (map F A Q ι s.val)‖ * _ = _
  rw [← parameterPower_pullback ι, parameterPower, Complex.norm_exp, complexParameterPairing_re]
  rfl

omit [NumberField F] in
/-- A slope that agrees on the split component with a character pullback has zero real part
there at an imaginary parameter. -/
theorem parameterRealPart_restrict_slope_imaginary
    (L : ComplexCharacterParameter F P →ₗ[ℂ] ComplexCharacterParameter F Q)
    (j : A ⟶ P) (hL : ∀ lam, parameterRestrict ι (L lam) = parameterRestrict j lam)
    (x : RealCharacterParameter F P) :
    parameterRealPart F A (parameterRestrict ι (L (imaginaryParameter F P x))) = 0 := by
  rw [hL, parameterRealPart_pullback, parameterRealPart_imaginaryParameter, map_zero]

/-- If the normalized offset restricts in real part to a finite combination of positive
relative roots with nonpositive coefficients, an affine label with imaginary slope on the
split component gives a raw exponent value bounded by the half modulus at every dominant
point. The empty sum covers the leading labels with zero normalized offset. -/
def EisensteinExponentLabelBoundStatement : Prop :=
  ∀ (L : ComplexCharacterParameter F P →ₗ[ℂ] ComplexCharacterParameter F Q),
    (∀ x : RealCharacterParameter F P,
      parameterRealPart F A (parameterRestrict ι (L (imaginaryParameter F P x))) = 0) →
    ∀ (mu : ComplexCharacterParameter F Q) {k : ℕ}
      (β : Fin k → characterLattice fam.T) (c : Fin k → ℝ),
      (∀ r, β r ∈ positiveRelativeRoots fam.i fam.ν) → (∀ r, c r ≤ 0) →
      parameterRealPart F A (parameterRestrict ι mu) = ∑ r, c r ⊗ₜ[ℤ] (fam.f J ≫ β r) →
      ∀ (x : RealCharacterParameter F P) (s : PositiveRealTorus.intrinsicSubgroup F (fam.A J)),
        fam.IsDominantSplitPoint J s →
        let a := PositiveRealTorus.positivePointMap F Q (fam.A J) ι s
        ‖parameterPower F Q (L (imaginaryParameter F P x) + (mu + halfModulusParameter F Q)) a‖ ≤
          ‖fam.halfModulus J a‖

/-- Dominance makes each positive-root logarithm nonnegative, so the normalized offset
contributes a factor at most one to the norm of the raw exponent. -/
theorem norm_parameterPower_affine_imaginary_le_halfModulus :
    fam.EisensteinExponentLabelBoundStatement (P := P) J := by
  intro L hL mu k β c hβ hc hmu x s hs
  dsimp only
  rw [← add_assoc, fam.norm_parameterPower_add_halfModulus_eq J, map_add, map_add, hL x, zero_add, hmu]
  have hpair : realParameterPairing F A (∑ r, c r ⊗ₜ[ℤ] (fam.f J ≫ β r))
      (characterLog F A s.val) ≤ 0 := by
    simp only [map_sum, LinearMap.sum_apply]
    exact Finset.sum_nonpos fun r _ => mul_nonpos_of_nonpos_of_nonneg (hc r)
      (fam.characterLog_restrict_nonneg_of_isDominantSplitPoint J hs (hβ r))
  calc
    _ ≤ Real.exp 0 * ‖fam.halfModulus J (PositiveRealTorus.positivePointMap F Q (fam.A J) ι s)‖ :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hpair) (norm_nonneg _)
    _ = _ := by rw [Real.exp_zero, one_mul]

end Langlands.Global.StandardParabolicFamily
