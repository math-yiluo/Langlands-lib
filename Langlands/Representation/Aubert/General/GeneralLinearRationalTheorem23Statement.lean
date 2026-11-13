import Langlands.Representation.Aubert.General.GeneralLinearRationalGraded

/-! # Actual rational-point GL form of Aubert Theorem 2.3

Statement targets only. The lower exactness, induction-ring laws and whole
segment-polynomial comparison remain explicit. These are transport targets for
actual exact K0; no theorem is supplied in this module.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped DirectSum CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily.GL

open GroupScheme SmoothRep GeneralLinear
open Langlands.AlgebraicGeometry.PointTopology

/-- Identify the conjugated unadjusted matrix operator with the literal
standard-family rational-point operator, with all comparison premises supplied
and arbitrary premise witnesses retained. -/
def RationalUnadjustedOperatorIdentificationStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData) (N : ℕ)
    (ν : cocharacterLattice
      (splitTorus.commGroupScheme (Spec (CommRingCat.of F.Carrier)) (ULift (Fin N))))
    (hν : StrictAnti (GroupScheme.GeneralLinear.cocharacterCoordEquiv (Fin N) F.Carrier ν)),
    letI := T.topology
    letI : IsTopologicalRing F.Carrier := by
      let := T.valuativeRel
      let := T.localField
      infer_instance
    letI : TopologicalSpace (RationalPoint F.Carrier
        (GroupScheme.GeneralLinear.groupScheme (Fin N) (CommRingCat.of F.Carrier)).X) :=
      pointTopology
    (LocallyCompactSpace (RationalPoint F.Carrier
        (GroupScheme.GeneralLinear.groupScheme (Fin N) (CommRingCat.of F.Carrier)).X) ∧
      NonarchimedeanGroup (RationalPoint F.Carrier
        (GroupScheme.GeneralLinear.groupScheme (Fin N) (CommRingCat.of F.Carrier)).X) ∧
      T2Space (RationalPoint F.Carrier
        (GroupScheme.GeneralLinear.groupScheme (Fin N) (CommRingCat.of F.Carrier)).X)) ∧
    ∀ [LocallyCompactSpace (RationalPoint F.Carrier
        (GroupScheme.GeneralLinear.groupScheme (Fin N) (CommRingCat.of F.Carrier)).X)]
      [NonarchimedeanGroup (RationalPoint F.Carrier
        (GroupScheme.GeneralLinear.groupScheme (Fin N) (CommRingCat.of F.Carrier)).X)]
      [T2Space (RationalPoint F.Carrier
        (GroupScheme.GeneralLinear.groupScheme (Fin N) (CommRingCat.of F.Carrier)).X)],
      let iD := GroupScheme.GeneralLinear.diagonalTorus (Fin N) (CommRingCat.of F.Carrier)
      let hgen : IsGenericCocharacter iD ν :=
        (GroupScheme.GeneralLinear.isGenericCocharacter_diagonalTorus_iff F.Carrier ν).mpr
          hν.injective
      let hG := isConnectedReductive_generalLinear F.Carrier (Fin N)
      let hi := GroupScheme.GeneralLinear.isMaximalSplitTorus_diagonalTorus (n := Fin N) F.Carrier
      let dec := isSemidirectDecomposition_of_standardCocharacterStatement iD ν
        standardCocharacter.{u} hG hi hgen
      (∃ hU : ∀ I, IsClosed (unipotent iD ν I : Set (RationalPoint F.Carrier
          (GroupScheme.GeneralLinear.groupScheme (Fin N) (CommRingCat.of F.Carrier)).X)),
        (∀ I, IsClosed (parabolic iD ν I : Set (RationalPoint F.Carrier
          (GroupScheme.GeneralLinear.groupScheme (Fin N) (CommRingCat.of F.Carrier)).X))) ∧
        (∀ I, Continuous (dec I).projection) ∧
        (∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent iD ν I)) ∧
        (∀ I, PreservesFiniteLength
          (normalizedInductionFunctor.{u, max (u + 1) v} (dec I) (hU I))) ∧
        (∀ I, PreservesFiniteLength (jacquetFunctor.{u, max (u + 1) v} (dec I) (hU I)))) ∧
      ∀ (hU : ∀ I, IsClosed (unipotent iD ν I : Set (RationalPoint F.Carrier
          (GroupScheme.GeneralLinear.groupScheme (Fin N) (CommRingCat.of F.Carrier)).X)))
        (hP : ∀ I, IsClosed (parabolic iD ν I : Set (RationalPoint F.Carrier
          (GroupScheme.GeneralLinear.groupScheme (Fin N) (CommRingCat.of F.Carrier)).X)))
        (hproj : ∀ I, Continuous (dec I).projection)
        (hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent iD ν I))
        (hiFl : ∀ I, PreservesFiniteLength
          (normalizedInductionFunctor.{u, max (u + 1) v} (dec I) (hU I)))
        (hrFl : ∀ I, PreservesFiniteLength
          (jacquetFunctor.{u, max (u + 1) v} (dec I) (hU I))),
        rationalUnadjustedOperator.{u, v} F T N =
          rationalAlternatingOperator iD ν standardCocharacter.{u} hG hi hgen hU hP hproj hUc
            hiFl hrFl
            (GroupScheme.GeneralLinear.hasRelativeRootSystem_diagonalTorus (n := Fin N)
              F.Carrier)

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData)

/-- Definition 2.1 on actual rational-point irreducibles, including the
support-presentation sign of Remark 2.2. -/
def RationalSupportAdjustmentStatement : Prop :=
  letI := T.topology
  letI : IsTopologicalRing F.Carrier := by
    let := T.valuativeRel
    let := T.localField
    infer_instance
  ∀ N : ℕ,
    letI := rationalGLTopology F T N
    let e := GroupScheme.GeneralLinear.rationalPointsContinuousMulEquiv N F.Carrier
    (∀ (E : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalGeneralLinear F N))
      (hE : E.IsIrreducible),
      let x := FiniteLengthGrothendieckGroup.ofRepresentation E
        (hasFiniteLength_of_isIrreducible hE)
      rationalAdjustedOperator.{u, v} F T N x =
        rationalSupportSign.{u, v} F T N E hE • rationalUnadjustedOperator.{u, v} F T N x) ∧
    (∀ (E : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalGeneralLinear F N))
      (hE : E.IsIrreducible) (B : BlockShape N)
      (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (B.Levi F.Carrier))
      (_hσ : σ.IsIrreducible),
      CuspidalSupport.IsLeviQuasicuspidal B σ.representation →
      IsSubquotient (SmoothRep.pullback e.symm E)
        ((T.normalizedParabolicInductionFunctor.{u, max (u + 1) v} B).obj σ) →
      rationalSupportSign.{u, v} F T N E hE = (-1 : ℤ) ^ (N - B.length))

/-- The complete rank-zero classes retain the existing GL convention. -/
def RationalRankZeroStatement : Prop :=
  letI := T.topology
  letI : IsTopologicalRing F.Carrier := by
    let := T.valuativeRel
    let := T.localField
    infer_instance
  letI := rationalGLTopology F T 0
  rationalUnadjustedOperator.{u, v} F T 0 = LinearMap.id ∧
    rationalAdjustedOperator.{u, v} F T 0 = LinearMap.id ∧
      ∀ (E : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalGeneralLinear F 0))
        (hE : E.IsIrreducible), rationalSupportSign.{u, v} F T 0 E hE = 1

/-- The whole graded operator restricts to the actual rankwise operator. -/
def RationalGradedHomogeneousStatement : Prop :=
  ∀ (N : ℕ) (x : RationalGLK0.{u, v} F T N),
    rationalGradedAdjustedOperator.{u, v} F T (rationalGradedInclusion.{u, v} F T N x) =
      rationalGradedInclusion.{u, v} F T N (rationalAdjustedOperator.{u, v} F T N x)

/-- Signed exchange for the actual pullbacks of every supplied strong segment
socle and special quotient. Finite-length witnesses are supplied by their
irreducibility and exact group pullback. -/
def RationalSegmentSocleHeadStatement : Prop :=
  letI := T.topology
  letI : IsTopologicalRing F.Carrier := by
    let := T.valuativeRel
    let := T.localField
    infer_instance
  ∀ (Δ : T.Segment.{max (u + 1) v, u})
    (πZ πS : SmoothRep.{0, u, max (u + 1) v} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hZ : T.IsSegmentSocle Δ πZ) (hS : T.IsSegmentHead Δ πS),
    letI := rationalGLTopology F T Δ.degree
    let e := GroupScheme.GeneralLinear.rationalPointsContinuousMulEquiv Δ.degree F.Carrier
    let hπZ := hasFiniteLength_of_isIrreducible (by
      obtain ⟨_, _, h⟩ := hZ
      exact h.1)
    let hπS := hasFiniteLength_of_isIrreducible (by
      obtain ⟨_, _, h⟩ := hS
      exact h.1)
    let x := FiniteLengthGrothendieckGroup.ofRepresentation (SmoothRep.pullback e πZ)
      (pullbackFunctor_preservesFiniteLength e πZ hπZ)
    let y := FiniteLengthGrothendieckGroup.ofRepresentation (SmoothRep.pullback e πS)
      (pullbackFunctor_preservesFiniteLength e πS hπS)
    rationalUnadjustedOperator.{u, v} F T Δ.degree x =
      (-1 : ℤ) ^ (Δ.degree - Δ.length) • y

variable (hx : Aubert.BinaryProductExactnessStatement.{u, max (u + 1) v} F T)
  (hl : Aubert.GradedInductionRingLawsStatement.{u, max (u + 1) v} F T hx)
  (hp : Aubert.SegmentPolynomialComparisonStatement.{u, max (u + 1) v} F T hx hl)

/-- Every class of the complete rational-point graded induction ring satisfies
the multiplicativity, involutivity and whole-ring Zelevinsky comparison. The
polynomial equivalence and the full monomial basis are explicitly identified
with the actual transported class evaluations. -/
def RationalWholeGradedTheorem23Statement : Prop :=
  letI := T.topology
  letI := Aubert.gradedInductionRing.{u, max (u + 1) v} F T hx hl
  letI := rationalGradedInductionRing.{u, v} F T hx hl
  let e := rationalGradedPullbackEquiv.{u, v} F T
  (∀ x y, rationalGradedAdjustedOperator.{u, v} F T (x * y) =
    rationalGradedAdjustedOperator.{u, v} F T x * rationalGradedAdjustedOperator.{u, v} F T y) ∧
    (rationalGradedAdjustedOperator.{u, v} F T 1 = 1) ∧
    Function.Involutive (rationalGradedAdjustedOperator.{u, v} F T) ∧
    Function.Involutive (rationalZelevinskyEndomorphism.{u, v} F T hx hl hp) ∧
    (rationalGradedAdjustedOperator.{u, v} F T =
      (rationalZelevinskyEndomorphism.{u, v} F T hx hl hp).toAddMonoidHom.toIntLinearMap) ∧
    (∀ P : MvPolynomial (T.Segment.{max (u + 1) v, u}) ℤ,
      rationalSegmentPolynomialEquiv.{u, v} F T hx hl hp P =
        e (Aubert.segmentPolynomialEvaluation.{u, max (u + 1) v} F T hx hl P)) ∧
    (∀ d : T.Segment.{max (u + 1) v, u} →₀ ℕ,
      rationalSegmentMonomialBasis.{u, v} F T hx hl hp d =
        e (Aubert.segmentMonomial.{u, max (u + 1) v} F T hx hl d))

/-- The actual rational-point GL target, over all p-adic fields and independent
field and representation universes, retaining the exact lower prerequisites. -/
def RationalTheorem23Statement : Prop :=
  RationalUnadjustedOperatorIdentificationStatement.{u, v} ∧
    ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData)
      (hx : Aubert.BinaryProductExactnessStatement.{u, max (u + 1) v} F T)
      (hl : Aubert.GradedInductionRingLawsStatement.{u, max (u + 1) v} F T hx)
      (hp : Aubert.SegmentPolynomialComparisonStatement.{u, max (u + 1) v} F T hx hl),
      RationalSupportAdjustmentStatement.{u, v} F T ∧
        RationalRankZeroStatement.{u, v} F T ∧
        RationalGradedHomogeneousStatement.{u, v} F T ∧
        RationalSegmentSocleHeadStatement.{u, v} F T ∧
        RationalWholeGradedTheorem23Statement.{u, v} F T hx hl hp

end Langlands.Aubert.General.RationalPointFamily.GL
