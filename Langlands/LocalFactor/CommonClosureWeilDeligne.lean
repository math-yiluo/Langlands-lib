import Langlands.LocalFactor.CommonClosureSpectral
import Langlands.LocalFactor.WeilDeligne
import Langlands.LocalField.Normalization.Proof

/-!
# Conditional Weil–Deligne factors on actual common-closure groups

The ordinary constant is evaluated from a supplied system. The correction is the
actual determinant on the invariant quotient, at an explicitly supplied geometric
Frobenius and the intermediate field's residue cardinality.
-/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.CommonClosureWeilDeligne

open CommonClosure CommonClosureSpectral Weil.Local
open VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Restriction of the actual base-field norm character. -/
def normCharacter (E : Extension F) : weilSubgroup F E →ₜ* ℂˣ where
  toMonoidHom := (localNormCharacter F).toMonoidHom.comp (weilSubgroup F E).subtype
  continuous_toFun := (localNormCharacter F).continuous.comp continuous_subtype_val

/-- Actual inertia inside the fixing subgroup, as the kernel of base degree. -/
abbrev inertia (E : Extension F) : Subgroup (weilSubgroup F E) :=
  (baseDegree F E).toMonoidHom.ker

/-- The norm agrees with the actual residue-normalized base degree character. -/
theorem normCharacter_apply (E : Extension F) (w : weilSubgroup F E) :
    (normCharacter F E w : ℂ) =
      (F.canonicalTopologicalData.residueCardinality : ℂ) ^
        (-(baseDegree F E w).toAdd) :=
  residueNormCharacter_apply _ _ _

/-- Equality of norm values determines the actual integer degree. -/
theorem degree_eq_of_normCharacter_eq (E : Extension F) {g h : weilSubgroup F E}
    (heq : normCharacter F E g = normCharacter F E h) :
    baseDegree F E g = baseDegree F E h := by
  have hv := congrArg (fun z : ℂˣ => ‖(z : ℂ)‖) heq
  simp only [normCharacter_apply, norm_zpow, Complex.norm_natCast] at hv
  have hq : (1 : ℝ) < (F.canonicalTopologicalData.residueCardinality : ℝ) := by
    exact_mod_cast F.canonicalTopologicalData.residueCardinality_gt_one
  have hn := zpow_right_injective₀ (lt_trans zero_lt_one hq) (ne_of_gt hq) hv
  change (baseDegree F E g).toAdd = (baseDegree F E h).toAdd
  exact neg_injective hn

/-- The actual intermediate-field residue cardinality, as a real number. -/
def residueCardinality (E : Extension F) : ℝ := (fieldData F E).residueCardinality

theorem residueCardinality_pos (E : Extension F) : 0 < residueCardinality F E := by
  have h : 1 < (fieldData F E).residueCardinality :=
    (fieldData F E).residueCardinality_gt_one
  change (0 : ℝ) < ((fieldData F E).residueCardinality : ℝ)
  exact_mod_cast (lt_trans Nat.zero_lt_one h)

/-- A supplied element with the actual norm of geometric Frobenius over `E`.
No existence, choice, or cross-closure comparison is asserted. -/
abbrev GeometricFrobenius (E : Extension F) :=
  {Φ : weilSubgroup F E // normCharacter F E Φ = (residueCardinalityUnit (fieldData F E))⁻¹}

/-- Two such lifts lie in the same actual inertia coset. -/
theorem frobenius_coset (E : Extension F) (Φ Ψ : GeometricFrobenius F E) :
    Ψ.val * Φ.val⁻¹ ∈ inertia F E := by
  have hd := degree_eq_of_normCharacter_eq F E (Ψ.property.trans Φ.property.symm)
  change baseDegree F E (Ψ.val * Φ.val⁻¹) = 1
  rw [map_mul, map_inv, hd, mul_inv_cancel]

/-- Actual pairs with the restricted arithmetic norm as covariance character. -/
abbrev Pair (E : Extension F) :=
  WeilDeligneRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F E)
    (normCharacter F E).toMonoidHom

/-- The ordinary exact virtual class of a continuous underlying representation. -/
def underlyingClass (E : Extension F) (A : Pair.{uF, uV} F E)
    (hA : A.toFiniteRepresentation.IsContinuous) : Virtual.{uF, uV} F E :=
  ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate F E)
    ⟨A.toFiniteRepresentation, hA⟩

theorem underlyingClass_eq_of_equiv (E : Extension F) {A B : Pair.{uF, uV} F E}
    (hA : A.toFiniteRepresentation.IsContinuous) (hB : B.toFiniteRepresentation.IsContinuous)
    (f : WeilDeligneRepresentation.Equiv A B) :
    underlyingClass F E A hA = underlyingClass F E B hB :=
  ExactGrothendieckGroup.ofRepresentation_eq_of_equiv _ f.representationEquiv

/-- The actual Euler reciprocal on `(ker N)^I`, retaining its rational poles. -/
def rationalLFactor (E : Extension F) (A : Pair.{uF, uV} F E)
    (Φ : GeometricFrobenius F E) : RatFunc ℂ :=
  WeilDeligne.rationalLFactor A (inertia F E) Φ.val

/-- The safe domain for `q_E^(-s)` evaluation. -/
abbrev SpectralRegularPoint (E : Extension F) (A : Pair.{uF, uV} F E)
    (Φ : GeometricFrobenius F E) :=
  WeilDeligne.SpectralRegularPoint A (inertia F E) Φ.val
    (residueCardinality F E) (residueCardinality_pos F E)

def spectralLValue (E : Extension F) (A : Pair.{uF, uV} F E)
    (Φ : GeometricFrobenius F E) (s : SpectralRegularPoint F E A Φ) : ℂˣ :=
  WeilDeligne.spectralLValue A (inertia F E) Φ.val
    (residueCardinality F E) (residueCardinality_pos F E) s

/-- The determinant on `V^I/(ker N)^I` evaluated at `q_E^(-s)`. -/
def quotientValue (E : Extension F) (A : Pair.{uF, uV} F E)
    (Φ : GeometricFrobenius F E) (s : ℂ) : ℂˣ :=
  WeilDeligne.quotientCorrectionValue A (inertia F E) Φ.val
    (spectralParameter (residueCardinality F E) (residueCardinality_pos F E) s)

theorem quotientValue_det (E : Extension F) (A : Pair.{uF, uV} F E)
    (Φ : GeometricFrobenius F E) (s : ℂ) :
    (quotientValue F E A Φ s : ℂ) =
      LinearMap.det ((Complex.exp (-s * (Real.log (residueCardinality F E) : ℂ))) •
        (-WeilDeligne.quotientOperator A (inertia F E) Φ.val)) :=
  WeilDeligne.quotientCorrectionValue_det _ _ _ _

/-- The complete measure-dependent spectral epsilon value, conditional on an
explicitly supplied system satisfying its exact property. -/
def conditionalEpsilonValue (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (A : Pair.{uF, uV} F E) (hA : A.toFiniteRepresentation.IsContinuous)
    (Φ : GeometricFrobenius F E) (s : ℂ) : ℂˣ :=
  conditionalDeligneValue F e ε hε E ψ μ (underlyingClass F E A hA) s *
    quotientValue F E A Φ s

/-- Pair equivalence preserves the quotient correction. -/
theorem quotientValue_eq_of_equiv (E : Extension F) {A B : Pair.{uF, uV} F E}
    (f : WeilDeligneRepresentation.Equiv A B) (Φ : GeometricFrobenius F E) (s : ℂ) :
    quotientValue F E A Φ s = quotientValue F E B Φ s := by
  apply Units.ext
  simp only [quotientValue, WeilDeligne.quotientCorrectionValue_eq_eval,
    WeilDeligne.quotientCorrectionPolynomial_eq_of_equiv (inertia F E) f]

/-- The correction is independent of the supplied Frobenius lift. -/
theorem quotientValue_eq_of_frobenius (E : Extension F) (A : Pair.{uF, uV} F E)
    (Φ Ψ : GeometricFrobenius F E) (s : ℂ) :
    quotientValue F E A Ψ s = quotientValue F E A Φ s := by
  apply Units.ext
  simp only [quotientValue, WeilDeligne.quotientCorrectionValue_eq_eval,
    WeilDeligne.quotientCorrectionPolynomial,
    WeilDeligne.quotientDeterminant_eq_of_coset A (inertia F E) (frobenius_coset F E Φ Ψ)]

/-- Vanishing monodromy makes the actual quotient correction one. -/
theorem quotientValue_eq_one_of_monodromy_zero (E : Extension F) (A : Pair.{uF, uV} F E)
    (hN : A.monodromy = 0) (Φ : GeometricFrobenius F E) (s : ℂ) :
    quotientValue F E A Φ s = 1 := by
  apply Units.ext
  rw [quotientValue, WeilDeligne.quotientCorrectionValue_eq_eval,
    WeilDeligne.quotientCorrectionPolynomial,
    WeilDeligne.conductorCorrection_eq_zero_of_monodromy_zero A (inertia F E) hN,
    WeilDeligne.quotientDeterminant_eq_one_of_monodromy_zero A (inertia F E) hN]
  simp

/-- Equivalence of actual pairs preserves the full conditional value. -/
theorem conditionalEpsilonValue_eq_of_equiv (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    {A B : Pair.{uF, uV} F E}
    (hA : A.toFiniteRepresentation.IsContinuous) (hB : B.toFiniteRepresentation.IsContinuous)
    (f : WeilDeligneRepresentation.Equiv A B) (Φ : GeometricFrobenius F E) (s : ℂ) :
    conditionalEpsilonValue F e ε hε E ψ μ A hA Φ s =
      conditionalEpsilonValue F e ε hε E ψ μ B hB Φ s := by
  simp only [conditionalEpsilonValue, underlyingClass_eq_of_equiv F E hA hB f,
    quotientValue_eq_of_equiv F E f]

/-- The full conditional value is independent of the supplied Frobenius lift. -/
theorem conditionalEpsilonValue_eq_of_frobenius (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (A : Pair.{uF, uV} F E) (hA : A.toFiniteRepresentation.IsContinuous)
    (Φ Ψ : GeometricFrobenius F E) (s : ℂ) :
    conditionalEpsilonValue F e ε hε E ψ μ A hA Ψ s =
      conditionalEpsilonValue F e ε hε E ψ μ A hA Φ s := by
  rw [conditionalEpsilonValue, conditionalEpsilonValue, quotientValue_eq_of_frobenius]

/-- At zero monodromy the full value reduces to the ordinary supplied-system value. -/
theorem conditionalEpsilonValue_of_monodromy_zero (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (A : Pair.{uF, uV} F E) (hA : A.toFiniteRepresentation.IsContinuous)
    (hN : A.monodromy = 0) (Φ : GeometricFrobenius F E) (s : ℂ) :
    conditionalEpsilonValue F e ε hε E ψ μ A hA Φ s =
      conditionalDeligneValue F e ε hε E ψ μ (underlyingClass F E A hA) s := by
  rw [conditionalEpsilonValue, quotientValue_eq_one_of_monodromy_zero F E A hN, mul_one]

end Langlands.LocalFactor.CommonClosureWeilDeligne
