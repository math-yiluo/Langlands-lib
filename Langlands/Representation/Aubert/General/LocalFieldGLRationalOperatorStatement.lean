import Langlands.Representation.Aubert.General.CanonicalRationalOperator
import Langlands.Representation.Aubert.General.GeneralLinearRationalIndexing
import Langlands.Group.GL.AlgebraicPointTopology
import Langlands.GroupScheme.Rational.GeneralLinearProof
import Langlands.GroupScheme.Reductive.GeneralLinear
import Langlands.AllField.Representation.Induction.Parabolic
import Langlands.AllField.Representation.Jacquet.Parabolic

/-! # The unadjusted GL operator over any nonarchimedean local field -/

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily.GL

open Langlands.AlgebraicGeometry.PointTopology
open GroupScheme SmoothRep

variable {F : Type u} [Field F] (T : LocalFieldData F) (n : ℕ)

/-- Finite length and short exact sequence preservation for the two actual
matrix functors in every block shape of rank `n`. -/
def LocalFieldMatrixParabolicExactLength : Prop :=
  letI := T.topology
  ∀ B : Langlands.GeneralLinear.BlockShape n,
    PreservesFiniteLength (T.normalizedParabolicInductionFunctor.{u, max (u + 1) v} B) ∧
    PreservesFiniteLengthShortExact (T.normalizedParabolicInductionFunctor.{u, max (u + 1) v} B) ∧
    PreservesFiniteLength (T.normalizedJacquetFunctor.{u, max (u + 1) v} B) ∧
    PreservesFiniteLengthShortExact (T.normalizedJacquetFunctor.{u, max (u + 1) v} B)

/-- Definition 1.5 on the exact finite-length matrix group. In the indexing
by block shapes the cardinality of the Levi root set is `n - B.length`. -/
def localFieldMatrixAlternatingOperator (h : LocalFieldMatrixParabolicExactLength.{u, v} T n) :
    letI := T.topology
    FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (Langlands.GeneralLinear n F) →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (Langlands.GeneralLinear n F) :=
  letI := T.topology
  letI : Fintype (Langlands.GeneralLinear.BlockShape n) := Fintype.ofFinite _
  ∑ B : Langlands.GeneralLinear.BlockShape n,
    ((-1 : ℤ) ^ (n - B.length)) •
      (FiniteLengthGrothendieckGroup.map (T.normalizedParabolicInductionFunctor B)
        (h B).1 (h B).2.1).comp
      (FiniteLengthGrothendieckGroup.map (T.normalizedJacquetFunctor B)
        (h B).2.2.1 (h B).2.2.2)

/-- The same two finite-length preservation inputs as the canonical general
operator give the matrix prerequisites and identify the operators by the
actual continuous rational-point equivalence. -/
def LocalFieldGLRationalOperatorComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] (T : LocalFieldData F) (n : ℕ)
    (ν : cocharacterLattice
      (splitTorus.commGroupScheme (Spec (CommRingCat.of F)) (ULift (Fin n))))
    (hν : StrictAnti (GroupScheme.GeneralLinear.cocharacterCoordEquiv (Fin n) F ν))
    (hiFl : DynamicInductionFiniteLengthStatement.{u, max (u + 1) v})
    (hrFl : DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v}),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    let G := GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)
    letI : TopologicalSpace (RationalPoint F G.X) := pointTopology
    let e := GroupScheme.GeneralLinear.rationalPointsContinuousMulEquiv n F
    let iD := GroupScheme.GeneralLinear.diagonalTorus (Fin n) (CommRingCat.of F)
    let hG := isConnectedReductive_generalLinear F (Fin n)
    let hi := GroupScheme.GeneralLinear.isMaximalSplitTorus_diagonalTorus (n := Fin n) F
    let hgen := (GroupScheme.GeneralLinear.isGenericCocharacter_diagonalTorus_iff F ν).mpr
      hν.injective
    let d := canonicalRationalAlternatingOperator.{u, v} hG iD ν hi hgen hiFl hrFl
    let p := FiniteLengthGrothendieckGroup.pullback.{u, u, max (u + 1) v} e
    LocalFieldMatrixParabolicExactLength.{u, v} T n ∧
      ∀ h : LocalFieldMatrixParabolicExactLength.{u, v} T n,
        p.comp (localFieldMatrixAlternatingOperator T n h) = d.comp p

end Langlands.Aubert.General.RationalPointFamily.GL
