import Langlands.Representation.CuspidalSupport.RationalNormKernelDecompositionStatement
import Langlands.Representation.CompactCoefficient.UniformSupportStatement

/-! # The common coefficient-support obligation in Renard VI.3.4 -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

/-- A compact support common to all compact irreducible norm-kernel coefficients
at each fixed compact-open level, with exactly the structural premises of the
published VI.3.4 finiteness target. -/
def RationalNormKernelUniformSupportStatement : Prop :=
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
      (ν : cocharacterLattice T) (_hν : IsGenericCocharacter i ν)
      (_hStandard : StandardCocharacterStatement.{uF})
      (_hRoots : HasRelativeRootSystem i)
      (_hU : ∀ I, IsClosed (unipotent i ν I : Set (GroupScheme.rationalPoints G))),
      ∀ K : OpenSubgroup (Plancherel.rationalCommonNormKernel G),
        IsCompact (K : Set (Plancherel.rationalCommonNormKernel G)) →
        CompactCoefficientClass.HasUniformFixedLevelCoefficientSupport.{uF, uV}
          K.toSubgroup

end Langlands.CuspidalSupport
