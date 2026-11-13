import Langlands.Representation.Aubert.General.RationalAlternatingOperator
import Langlands.Representation.Aubert.AlternatingOperator
import Langlands.Representation.Smooth.FiniteLengthGrothendieckTransport
import Langlands.Group.GL.AlgebraicPointTopology
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.GeneralLinearProof
import Langlands.GroupScheme.Rational.GeneralLinearGenericCentralizer
import Langlands.GroupScheme.Reductive.GeneralLinear

/-! # The rational-point GL operator is the matrix GL operator

Statement only. For a p-adic field `F` with topological data `T`, the group
scheme `GL_N` over `F`, its diagonal maximal split torus and a cocharacter with
strictly decreasing weights, the unadjusted alternating operator built from the
rational-point standard parabolic family is identified with the existing GL
operator `Langlands.Aubert.alternatingOperator F T N` by exact-K0 pullback along
the canonical continuous isomorphism from rational points to matrices.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily.GL

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology
open SmoothRep

/-- The rational-point/matrix comparison of Aubert's unadjusted operator for
`GL_N` over a p-adic field.

For every p-adic field `F` with topological data `T`, every rank `N`, and
every cocharacter `ν` of the diagonal torus of the group scheme `GL_N` whose
weights are strictly decreasing, equip the rational points of `GL_N` with the
canonical evaluation topology `pointTopology`. Then:

1. these points form a locally compact, Hausdorff, nonarchimedean group;
2. the premises of `rationalAlternatingOperator` hold for the standard rational
   family of the diagonal torus and `ν`: closed unipotent radicals, closed
   parabolics, continuous Levi projections, radicals that are limits of compact
   subgroups, and finite-length preservation by normalized induction and
   normalized Jacquet restriction at carrier universe `max (u + 1) v`;
3. for all such premise proofs, exact-K0 pullback along the canonical continuous
   isomorphism `rationalPointsContinuousMulEquiv N F.Carrier` intertwines the
   GL operator `Langlands.Aubert.alternatingOperator F T N` with
   `rationalAlternatingOperator`. -/
def RationalAlternatingOperatorComparisonStatement : Prop :=
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
        (FiniteLengthGrothendieckGroup.pullback.{u, u, max (u + 1) v}
            (GroupScheme.GeneralLinear.rationalPointsContinuousMulEquiv N F.Carrier)).comp
            (Aubert.alternatingOperator.{u, max (u + 1) v} F T N) =
          (rationalAlternatingOperator iD ν standardCocharacter.{u} hG hi hgen hU hP hproj hUc
              hiFl hrFl
              (GroupScheme.GeneralLinear.hasRelativeRootSystem_diagonalTorus (n := Fin N)
                F.Carrier)).comp
            (FiniteLengthGrothendieckGroup.pullback
              (GroupScheme.GeneralLinear.rationalPointsContinuousMulEquiv N F.Carrier))

end Langlands.Aubert.General.RationalPointFamily.GL
