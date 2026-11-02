import Langlands.Representation.Aubert.ZelevinskyPolynomial
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Additive and multiplicative extension to the whole actual graded ring

These are internal extension constructions for a family of homogeneous K0
operators. The later adjusted-Aubert target specializes that family to the
actual support-adjusted operator; no representation-theoretic condition for
that operator is proved merely by the algebraic extension.
-/

noncomputable section

namespace Langlands.Aubert

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
variable (D : letI := T.topology
  ∀ n, GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier →ₗ[ℤ]
    GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier)
variable (hx : BinaryProductExactnessStatement.{uF, uV} F T)

/-- The homogeneous multiplicativity condition, with the actual binary product. -/
def HomogeneousOperatorMultiplicativityStatement : Prop :=
  letI := T.topology
  ∀ a b x y,
    D (a + b) (binaryProductK0 F T hx a b x y) =
      binaryProductK0 F T hx a b (D a x) (D b y)

/-- Multiplicativity on all actual graded classes. -/
def GradedOperatorMultiplicativityStatement : Prop :=
  letI := T.topology
  ∀ x y, gradedOperator F T D (gradedMultiplication F T hx x y) =
    gradedMultiplication F T hx (gradedOperator F T D x) (gradedOperator F T D y)

/-- Homogeneous multiplicativity extends to the whole direct sum by bilinearity. -/
theorem gradedOperator_multiplicative_of_homogeneous
    (hm : HomogeneousOperatorMultiplicativityStatement F T D hx) :
    GradedOperatorMultiplicativityStatement F T D hx := by
  let := T.topology
  let m := gradedMultiplication F T hx
  let d := gradedOperator F T D
  have he : m.compr₂ d = m.compl₁₂ d d := by
    apply DirectSum.linearMap_ext
    intro a
    apply LinearMap.ext
    intro x
    apply DirectSum.linearMap_ext
    intro b
    apply LinearMap.ext
    intro y
    change gradedOperator F T D
        (gradedMultiplication F T hx (gradedInclusion F T a x) (gradedInclusion F T b y)) =
      gradedMultiplication F T hx
        (gradedOperator F T D (gradedInclusion F T a x))
        (gradedOperator F T D (gradedInclusion F T b y))
    rw [gradedMultiplication_homogeneous, gradedOperator_homogeneous,
      gradedOperator_homogeneous, gradedOperator_homogeneous,
      gradedMultiplication_homogeneous, hm a b x y]
  intro x y
  exact LinearMap.congr_fun (LinearMap.congr_fun he x) y

/-- Preservation of the actual graded rank-zero unit. -/
def GradedOperatorUnitStatement : Prop :=
  letI := T.topology
  gradedOperator F T D (gradedUnit F T) = gradedUnit F T

/-- The adjusted segment exchange that will be required of the operator family. -/
def GradedOperatorSegmentExchangeStatement : Prop :=
  letI := T.topology
  ∀ Δ : T.Segment.{max uF uV, uF},
    gradedOperator F T D (gradedSegmentSocle F T Δ) = gradedSegmentSpecial F T Δ

variable (hl : GradedInductionRingLawsStatement F T hx)

/-- A whole-ring endomorphism from the actual additive extension once its
explicit multiplicativity and unit conditions are proved. -/
def gradedOperatorRingHom
    (hm : GradedOperatorMultiplicativityStatement F T D hx)
    (hu : GradedOperatorUnitStatement F T D) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    GradedGrothendieckGroup.{uF, uV} F T →+* GradedGrothendieckGroup.{uF, uV} F T :=
  letI := T.topology
  letI := gradedInductionRing F T hx hl
  { toFun := gradedOperator F T D
    map_zero' := (gradedOperator F T D).map_zero
    map_add' := (gradedOperator F T D).map_add
    map_one' := hu
    map_mul' := hm }

/-- Additive maps agreeing on the spanning segment monomials agree on every
actual graded class. Individual segment generators alone are insufficient. -/
theorem gradedLinearMap_ext_monomials
    (hs : SegmentMonomialSpanningStatement F T hx hl) :
    letI := T.topology
    ∀ {f g : GradedGrothendieckGroup.{uF, uV} F T →ₗ[ℤ]
        GradedGrothendieckGroup.{uF, uV} F T},
      (∀ m, f (segmentMonomial F T hx hl m) = g (segmentMonomial F T hx hl m)) →
        f = g := by
  let := T.topology
  intro f g h
  exact LinearMap.ext_on_range hs h

/-- The polynomial universal property supplies the whole-ring comparison:
an actual additive extension satisfying the unit, product and segment formulas
equals the constructed Zelevinsky endomorphism on all classes. -/
theorem gradedOperatorRingHom_eq_zelevinsky
    (hp : SegmentPolynomialComparisonStatement F T hx hl)
    (hm : GradedOperatorMultiplicativityStatement F T D hx)
    (hu : GradedOperatorUnitStatement F T D)
    (hs : GradedOperatorSegmentExchangeStatement F T D) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    gradedOperatorRingHom F T D hx hl hm hu = zelevinskyEndomorphism F T hx hl hp := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  let e := segmentPolynomialEquiv F T hx hl hp
  let q := gradedOperatorRingHom F T D hx hl hm hu
  have he : q.comp e.toRingHom = segmentSpecialPolynomialEvaluation F T hx hl := by
    apply MvPolynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · intro Δ
      change q (segmentPolynomialEvaluation F T hx hl (MvPolynomial.X Δ)) =
        segmentSpecialPolynomialEvaluation F T hx hl (MvPolynomial.X Δ)
      rw [show segmentPolynomialEvaluation F T hx hl (MvPolynomial.X Δ) =
          gradedSegmentSocle F T Δ from MvPolynomial.eval₂Hom_X' _ _ _]
      rw [show segmentSpecialPolynomialEvaluation F T hx hl (MvPolynomial.X Δ) =
          gradedSegmentSpecial F T Δ from MvPolynomial.eval₂Hom_X' _ _ _]
      exact hs Δ
  apply RingHom.ext
  intro x
  obtain ⟨P, rfl⟩ := e.surjective x
  change q (e P) = segmentSpecialPolynomialEvaluation F T hx hl (e.symm (e P))
  rw [e.symm_apply_apply]
  exact RingHom.congr_fun he P

end Langlands.Aubert
