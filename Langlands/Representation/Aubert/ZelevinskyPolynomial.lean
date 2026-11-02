import Langlands.Representation.Aubert.SegmentGrothendieck
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Segment polynomials and the whole-ring Zelevinsky endomorphism

Polynomial evaluation lands in the actual graded exact-K0 ring. Its
bijectivity is the missing Corollary 7.5 comparison target. Given that
comparison, substitution of actual special-quotient classes constructs the
Zelevinsky ring endomorphism. Its involutivity is a separate exact target.
-/

noncomputable section

open scoped TensorProduct

namespace Langlands.Aubert

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
variable (hx : BinaryProductExactnessStatement.{uF, uV} F T)
  (hl : GradedInductionRingLawsStatement F T hx)

/-- Evaluation of segment variables at actual graded segment-socle classes. -/
def segmentPolynomialEvaluation :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    MvPolynomial (T.Segment.{max uF uV, uF}) ℤ →+*
      GradedGrothendieckGroup.{uF, uV} F T :=
  letI := T.topology
  letI := gradedInductionRing F T hx hl
  MvPolynomial.eval₂Hom (Int.castRingHom _) (gradedSegmentSocle F T)

/-- The exact polynomial-ring comparison required from Ze80 Corollary 7.5.
This is bijectivity of the actual class evaluation, not an abstract ring model. -/
def SegmentPolynomialComparisonStatement : Prop :=
  letI := T.topology
  letI := gradedInductionRing F T hx hl
  Function.Bijective (segmentPolynomialEvaluation F T hx hl)

/-- The induction monomial associated to a finite multiset of segment variables,
represented by its finite multiplicity function. The zero function gives the unit. -/
def segmentMonomial (d : T.Segment.{max uF uV, uF} →₀ ℕ) :
    GradedGrothendieckGroup.{uF, uV} F T :=
  letI := T.topology
  letI := gradedInductionRing F T hx hl
  segmentPolynomialEvaluation F T hx hl (MvPolynomial.monomial d 1)

/-- The precise additive spanning obligation is about all segment monomials. -/
def SegmentMonomialSpanningStatement : Prop :=
  letI := T.topology
  Submodule.span ℤ (Set.range (segmentMonomial F T hx hl)) = ⊤

/-- The full additive basis obligation: independence and spanning of monomials. -/
def SegmentMonomialBasisStatement : Prop :=
  letI := T.topology
  LinearIndependent ℤ (segmentMonomial F T hx hl) ∧
    SegmentMonomialSpanningStatement F T hx hl

variable (hp : SegmentPolynomialComparisonStatement F T hx hl)

/-- The polynomial comparison equivalence constructed from its exact target. -/
def segmentPolynomialEquiv :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    MvPolynomial (T.Segment.{max uF uV, uF}) ℤ ≃+*
      GradedGrothendieckGroup.{uF, uV} F T :=
  letI := T.topology
  letI := gradedInductionRing F T hx hl
  RingEquiv.ofBijective (segmentPolynomialEvaluation F T hx hl) hp

/-- The actual monomial basis, conditional on the polynomial comparison proof. -/
def segmentMonomialBasis :
    letI := T.topology
    Module.Basis (T.Segment.{max uF uV, uF} →₀ ℕ) ℤ
      (GradedGrothendieckGroup.{uF, uV} F T) :=
  letI := T.topology
  letI := gradedInductionRing F T hx hl
  (MvPolynomial.basisMonomials _ ℤ).map
    (segmentPolynomialEquiv F T hx hl hp).toAddEquiv.toIntLinearEquiv

@[simp]
theorem segmentMonomialBasis_apply (d : T.Segment.{max uF uV, uF} →₀ ℕ) :
    letI := T.topology
    segmentMonomialBasis F T hx hl hp d = segmentMonomial F T hx hl d := rfl

/-- Substitution of actual special-quotient classes for the segment variables. -/
def segmentSpecialPolynomialEvaluation :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    MvPolynomial (T.Segment.{max uF uV, uF}) ℤ →+*
      GradedGrothendieckGroup.{uF, uV} F T :=
  letI := T.topology
  letI := gradedInductionRing F T hx hl
  MvPolynomial.eval₂Hom (Int.castRingHom _) (gradedSegmentSpecial F T)

/-- Zelevinsky's whole-ring endomorphism of §9.12, constructed by polynomial
substitution using the actual segment classes and the exact comparison. -/
def zelevinskyEndomorphism :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    GradedGrothendieckGroup.{uF, uV} F T →+*
      GradedGrothendieckGroup.{uF, uV} F T :=
  letI := T.topology
  letI := gradedInductionRing F T hx hl
  (segmentSpecialPolynomialEvaluation F T hx hl).comp
    (segmentPolynomialEquiv F T hx hl hp).symm.toRingHom

@[simp]
theorem zelevinskyEndomorphism_segmentSocle (Δ : T.Segment.{max uF uV, uF}) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    zelevinskyEndomorphism F T hx hl hp (gradedSegmentSocle F T Δ) =
      gradedSegmentSpecial F T Δ := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  have hX : segmentPolynomialEquiv F T hx hl hp (MvPolynomial.X Δ) =
      gradedSegmentSocle F T Δ :=
    MvPolynomial.eval₂Hom_X' _ _ _
  change segmentSpecialPolynomialEvaluation F T hx hl
    ((segmentPolynomialEquiv F T hx hl hp).symm (gradedSegmentSocle F T Δ)) = _
  rw [← hX, RingEquiv.symm_apply_apply]
  exact MvPolynomial.eval₂Hom_X' _ _ _

/-- The remaining Ze80 §9.12 involutivity target on every actual graded class. -/
def ZelevinskyInvolutivityStatement : Prop :=
  letI := T.topology
  letI := gradedInductionRing F T hx hl
  Function.Involutive (zelevinskyEndomorphism F T hx hl hp)

/-- The whole-ring involution constructed once the exact involutivity target
is proved. Its underlying endomorphism is the above polynomial substitution. -/
def zelevinskyRingInvolution (hi : ZelevinskyInvolutivityStatement F T hx hl hp) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    GradedGrothendieckGroup.{uF, uV} F T ≃+*
      GradedGrothendieckGroup.{uF, uV} F T :=
  letI := T.topology
  letI := gradedInductionRing F T hx hl
  { toFun := zelevinskyEndomorphism F T hx hl hp
    invFun := zelevinskyEndomorphism F T hx hl hp
    left_inv := hi
    right_inv := hi
    map_mul' := (zelevinskyEndomorphism F T hx hl hp).map_mul
    map_add' := (zelevinskyEndomorphism F T hx hl hp).map_add }

end Langlands.Aubert
