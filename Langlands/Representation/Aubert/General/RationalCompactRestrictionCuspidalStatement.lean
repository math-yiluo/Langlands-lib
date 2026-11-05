import Langlands.Representation.CuspidalSupport.RationalWholeCuspidalDecompositionStatement
import Langlands.Representation.CompactCoefficient.Classes
import Langlands.Representation.CompactCoefficient.AmbientProjector

/-!
# General compact-restriction converse of Renard VI.2.1

This proposition states VI.2.1(c) implies (a) at the structural telescope of
the whole-category VI.3.5 target. Its proof is a separate obligation; the
converse is not an additional premise of that target.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

universe uF uV

/-- Renard VI.2.1(c) implies (a), for every actual smooth rational-point
representation, using the structural telescope of whole-category VI.3.5. -/
def RationalCompactRestrictionCuspidalStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    ∀ [LocallyCompactSpace (GroupScheme.rationalPoints G)]
      [NonarchimedeanGroup (GroupScheme.rationalPoints G)]
      [T2Space (GroupScheme.rationalPoints G)]
      (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{uF})
      (hRoots : HasRelativeRootSystem i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (GroupScheme.rationalPoints G))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      let h := isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν
      ∀ A : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G),
        HasCompactSmoothDualCoefficients
          (SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel G) A).representation →
        IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU A

end Langlands.Aubert.General.RationalPointFamily
