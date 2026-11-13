import Langlands.Representation.Aubert.General.GeneralLinearRationalComparisonProof
import Langlands.Representation.Aubert.ZelevinskyComparison

/-! # Graded exact K0 on actual rational-point general linear groups

Transport the published matrix GL constructions along the canonical continuous
group equivalences. The carriers are the exact Grothendieck groups of the actual
rational-point groups. Identification of the transported unadjusted operator with
the literal standard-family operator and Theorem 2.3 are separate targets.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped DirectSum CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily.GL

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData)

/-- The actual rational points of the group scheme GL_N. -/
abbrev RationalGeneralLinear (N : ℕ) :=
  RationalPoint F.Carrier
    (GroupScheme.GeneralLinear.groupScheme (Fin N) (CommRingCat.of F.Carrier)).X

/-- Canonical evaluation topology, using the supplied p-adic field topology. -/
@[instance_reducible]
def rationalGLTopology (N : ℕ) : TopologicalSpace (RationalGeneralLinear F N) :=
  letI := T.topology
  letI : IsTopologicalRing F.Carrier := by
    let := T.valuativeRel
    let := T.localField
    infer_instance
  pointTopology

/-- Exact finite-length K0 of actual smooth complex rational-point modules. -/
abbrev RationalGLK0 (N : ℕ) :=
  letI := rationalGLTopology F T N
  FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (RationalGeneralLinear F N)

/-- Exact-K0 pullback along the canonical rational-point/matrix group isomorphism. -/
def rationalGLPullbackEquiv (N : ℕ) :
    letI := T.topology
    GeneralLinear.FiniteLengthGrothendieckGroup.{max (u + 1) v, u} N F.Carrier ≃ₗ[ℤ]
      RationalGLK0.{u, v} F T N :=
  letI := T.topology
  letI : IsTopologicalRing F.Carrier := by
    let := T.valuativeRel
    let := T.localField
    infer_instance
  letI := rationalGLTopology F T N
  FiniteLengthGrothendieckGroup.pullbackEquiv
    (GroupScheme.GeneralLinear.rationalPointsContinuousMulEquiv N F.Carrier)

/-- The unadjusted matrix operator transported to actual rational-point exact K0. -/
def rationalUnadjustedOperator (N : ℕ) :
    RationalGLK0.{u, v} F T N →ₗ[ℤ] RationalGLK0.{u, v} F T N :=
  letI := T.topology
  let e := rationalGLPullbackEquiv.{u, v} F T N
  e.toLinearMap.comp
    ((Aubert.alternatingOperator.{u, max (u + 1) v} F T N).comp e.symm.toLinearMap)

/-- The support sign of an actual rational-point irreducible, read after
inverse pullback to the matrix model. -/
def rationalSupportSign (N : ℕ) :
    letI := rationalGLTopology F T N
    ∀ (E : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalGeneralLinear F N)),
      E.IsIrreducible → ℤ :=
  letI := T.topology
  letI : IsTopologicalRing F.Carrier := by
    let := T.valuativeRel
    let := T.localField
    infer_instance
  letI := rationalGLTopology F T N
  fun E hE =>
    let e := GroupScheme.GeneralLinear.rationalPointsContinuousMulEquiv N F.Carrier
    let M := SmoothRep.pullback e.symm E
    let hM : M.IsIrreducible :=
      (Langlands.isIrreducible_comp_continuousMulEquiv_iff E.representation e.symm).mpr hE
    Aubert.supportSign.{u, max (u + 1) v} F T N (SmoothRep.irreducibleIsoClass M hM)

/-- The support-adjusted operator transported to actual rational-point exact K0. -/
def rationalAdjustedOperator (N : ℕ) :
    RationalGLK0.{u, v} F T N →ₗ[ℤ] RationalGLK0.{u, v} F T N :=
  letI := T.topology
  let e := rationalGLPullbackEquiv.{u, v} F T N
  e.toLinearMap.comp
    ((Aubert.adjustedOperator.{u, max (u + 1) v} F T N).comp e.symm.toLinearMap)

/-- The direct sum of the actual rational-point exact K0 groups in all ranks. -/
abbrev RationalGradedGrothendieckGroup := ⨁ N : ℕ, RationalGLK0.{u, v} F T N

/-- Homogeneous inclusion, with rank zero retained. -/
def rationalGradedInclusion (N : ℕ) :
    RationalGLK0.{u, v} F T N →ₗ[ℤ] RationalGradedGrothendieckGroup.{u, v} F T :=
  DirectSum.lof ℤ ℕ (RationalGLK0.{u, v} F T) N

/-- The direct sum of the canonical exact-K0 pullback equivalences. -/
def rationalGradedPullbackEquiv :
    letI := T.topology
    Aubert.GradedGrothendieckGroup.{u, max (u + 1) v} F T ≃ₗ[ℤ]
      RationalGradedGrothendieckGroup.{u, v} F T :=
  letI := T.topology
  DirectSum.congrLinearEquiv (rationalGLPullbackEquiv.{u, v} F T)

/-- Whole graded adjusted operator on actual rational-point exact K0. -/
def rationalGradedAdjustedOperator :
    RationalGradedGrothendieckGroup.{u, v} F T →ₗ[ℤ]
      RationalGradedGrothendieckGroup.{u, v} F T :=
  letI := T.topology
  let e := rationalGradedPullbackEquiv.{u, v} F T
  e.toLinearMap.comp
    ((Aubert.gradedAdjustedOperator.{u, max (u + 1) v} F T).comp e.symm.toLinearMap)

variable (hx : Aubert.BinaryProductExactnessStatement.{u, max (u + 1) v} F T)

/-- Transport of the actual normalized induction multiplication, bilinear on
the original exact-K0 additive groups. -/
def rationalGradedMultiplication :
    RationalGradedGrothendieckGroup.{u, v} F T →ₗ[ℤ]
      RationalGradedGrothendieckGroup.{u, v} F T →ₗ[ℤ]
        RationalGradedGrothendieckGroup.{u, v} F T :=
  letI := T.topology
  let e := rationalGradedPullbackEquiv.{u, v} F T
  ((Aubert.gradedMultiplication.{u, max (u + 1) v} F T hx).compl₁₂ e.symm.toLinearMap e.symm.toLinearMap).compr₂
    e.toLinearMap

/-- The pulled-back actual trivial line in rank zero. -/
def rationalGradedUnit : RationalGradedGrothendieckGroup.{u, v} F T :=
  letI := T.topology
  rationalGradedPullbackEquiv.{u, v} F T (Aubert.gradedUnit.{u, max (u + 1) v} F T)

variable (hl : Aubert.GradedInductionRingLawsStatement.{u, max (u + 1) v} F T hx)

/-- The induction ring, retaining the existing exact-K0 additive group. -/
@[instance_reducible]
def rationalGradedInductionRing
    (hx : Aubert.BinaryProductExactnessStatement.{u, max (u + 1) v} F T)
    (hl : Aubert.GradedInductionRingLawsStatement.{u, max (u + 1) v} F T hx) :
    CommRing (RationalGradedGrothendieckGroup.{u, v} F T) := by
  letI := T.topology
  let e := rationalGradedPullbackEquiv.{u, v} F T
  let m := rationalGradedMultiplication.{u, v} F T hx
  have hm (x y) :
      e.symm (m x y) = Aubert.gradedMultiplication.{u, max (u + 1) v} F T hx (e.symm x) (e.symm y) := by
    exact e.symm_apply_apply _
  have hu : e.symm (rationalGradedUnit.{u, v} F T) = Aubert.gradedUnit.{u, max (u + 1) v} F T :=
    e.symm_apply_apply _
  exact
  { toAddCommGroup := inferInstance
    mul := fun x y => m x y
    one := rationalGradedUnit.{u, v} F T
    mul_assoc := fun x y z => e.symm.injective (by
      change e.symm (m (m x y) z) = e.symm (m x (m y z))
      rw [hm, hm, hm, hm]
      exact hl.1 _ _ _)
    mul_comm := fun x y => e.symm.injective (by
      change e.symm (m x y) = e.symm (m y x)
      rw [hm, hm]
      exact hl.2.1 _ _)
    one_mul := fun x => e.symm.injective (by
      change e.symm (m (rationalGradedUnit.{u, v} F T) x) = e.symm x
      rw [hm, hu]
      exact hl.2.2.1 _)
    mul_one := fun x => e.symm.injective (by
      change e.symm (m x (rationalGradedUnit.{u, v} F T)) = e.symm x
      rw [hm, hu]
      exact hl.2.2.2 _)
    left_distrib := fun x y z => (m x).map_add y z
    right_distrib := fun x y z => m.map_add₂ x y z
    zero_mul := fun x => m.map_zero₂ x
    mul_zero := fun x => (m x).map_zero }

/-- The canonical equivalence of the complete matrix and rational-point
induction rings. -/
def rationalGradedRingEquiv :
    letI := T.topology
    letI := Aubert.gradedInductionRing.{u, max (u + 1) v} F T hx hl
    letI := rationalGradedInductionRing.{u, v} F T hx hl
    Aubert.GradedGrothendieckGroup.{u, max (u + 1) v} F T ≃+*
      RationalGradedGrothendieckGroup.{u, v} F T := by
  letI := T.topology
  letI := Aubert.gradedInductionRing.{u, max (u + 1) v} F T hx hl
  letI := rationalGradedInductionRing.{u, v} F T hx hl
  let e := rationalGradedPullbackEquiv.{u, v} F T
  exact
  { e.toAddEquiv with
    map_mul' := fun x y => by
      change e (Aubert.gradedMultiplication.{u, max (u + 1) v} F T hx x y) =
        e (Aubert.gradedMultiplication.{u, max (u + 1) v} F T hx (e.symm (e x)) (e.symm (e y)))
      rw [e.symm_apply_apply, e.symm_apply_apply] }

variable (hp : Aubert.SegmentPolynomialComparisonStatement.{u, max (u + 1) v} F T hx hl)

/-- Whole polynomial-ring comparison using actual pulled-back segment classes. -/
def rationalSegmentPolynomialEquiv :
    letI := T.topology
    letI := rationalGradedInductionRing.{u, v} F T hx hl
    MvPolynomial (T.Segment.{max (u + 1) v, u}) ℤ ≃+*
      RationalGradedGrothendieckGroup.{u, v} F T :=
  letI := T.topology
  letI := Aubert.gradedInductionRing.{u, max (u + 1) v} F T hx hl
  letI := rationalGradedInductionRing.{u, v} F T hx hl
  (Aubert.segmentPolynomialEquiv.{u, max (u + 1) v} F T hx hl hp).trans (rationalGradedRingEquiv.{u, v} F T hx hl)

/-- The complete additive basis of pulled-back segment monomials. -/
def rationalSegmentMonomialBasis :
    letI := T.topology
    Module.Basis (T.Segment.{max (u + 1) v, u} →₀ ℕ) ℤ
      (RationalGradedGrothendieckGroup.{u, v} F T) :=
  letI := T.topology
  (Aubert.segmentMonomialBasis.{u, max (u + 1) v} F T hx hl hp).map (rationalGradedPullbackEquiv.{u, v} F T)

/-- Zelevinsky polynomial substitution transported to the complete actual
rational-point induction ring. -/
def rationalZelevinskyEndomorphism :
    letI := T.topology
    letI := rationalGradedInductionRing.{u, v} F T hx hl
    RationalGradedGrothendieckGroup.{u, v} F T →+*
      RationalGradedGrothendieckGroup.{u, v} F T :=
  letI := T.topology
  letI := Aubert.gradedInductionRing.{u, max (u + 1) v} F T hx hl
  letI := rationalGradedInductionRing.{u, v} F T hx hl
  let e := rationalGradedRingEquiv.{u, v} F T hx hl
  e.toRingHom.comp ((Aubert.zelevinskyEndomorphism.{u, max (u + 1) v} F T hx hl hp).comp e.symm.toRingHom)

end Langlands.Aubert.General.RationalPointFamily.GL
