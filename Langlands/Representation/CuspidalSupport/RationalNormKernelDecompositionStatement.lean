import Langlands.Representation.CuspidalSupport.RationalNormKernelCategory
import Langlands.Representation.CuspidalSupport.RationalCuspidalInertiaFinitenessStatement

/-!
# Renard VI.3.4: norm-kernel finiteness and category decomposition

Both targets concern the actual common rational-character norm kernel with its
canonical subtype topology. Finiteness and decomposition are conclusions, with
the same explicit structural premises as the neighboring inertia targets.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

/-- The condition (KF) verified in the proof of VI.3.4: each compact open
subgroup of the actual norm kernel fixes nonzero vectors in only finitely many
compact irreducible smooth isomorphism classes. -/
def RationalNormKernelFixedLevelFinitenessStatement : Prop :=
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
        (CompactCoefficientClass.fixedStratum.{uF, uV} K.toSubgroup).Finite

/-- The category decomposition of VI.3.4 into all compact-class direct-sum
factors and the factor with no nonzero compact actual subquotient. -/
def RationalNormKernelCategoryDecompositionStatement : Prop :=
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
      IsRationalNormKernelCategoryDecomposition.{uF, uV} G

end Langlands.CuspidalSupport
