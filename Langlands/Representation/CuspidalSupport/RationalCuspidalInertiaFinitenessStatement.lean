import Langlands.Representation.CuspidalSupport.RationalInertiaDecompositionStatement

/-!
# Renard VI.3.4: finiteness of cuspidal inertia classes with fixed vectors

This is the concluding remark of VI.3.4, on the actual rational-point group
and the existing quotient by actual unramified twists. The finite set consists
of classes having an irreducible proper-standard-cuspidal representative with
nonzero fixed vectors for the given compact open subgroup. No finiteness or
decomposition conclusion is assumed.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

/-- For every compact open subgroup of the actual rational-point group, only
finitely many inertia classes have an irreducible cuspidal representative with
nonzero fixed vectors. Cuspidality is tested on every proper actual standard
parabolic, with the same explicit structural inputs as VI.3.3.1. -/
def RationalCuspidalInertiaFinitenessStatement : Prop :=
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
      ∀ K : OpenSubgroup (GroupScheme.rationalPoints G),
        IsCompact (K : Set (GroupScheme.rationalPoints G)) →
        Set.Finite
          {c : RationalIrreducibleInertiaClass.{uF, uV} G |
            ∃ (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
              (hπ : π.IsIrreducible),
              IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU π ∧
              rationalIrreducibleInertiaClass G π hπ = c ∧
              Nontrivial (fixedVectors π.representation K.toSubgroup)}

end Langlands.CuspidalSupport
