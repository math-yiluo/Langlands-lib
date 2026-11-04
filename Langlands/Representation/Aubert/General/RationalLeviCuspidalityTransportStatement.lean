import Langlands.Representation.Aubert.General.RationalLeviNormTopology
import Langlands.Representation.Aubert.General.CuspidalityTransport
import Langlands.GroupScheme.Rational.StandardLeviTorusFactor
import Langlands.GroupScheme.Rational.StandardCocharacterStatement
import Langlands.GroupScheme.Dynamic.LieStatement

/-! # Cuspidality on an actual standard Levi and on its literal point subgroup -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

/-- The canonical point homeomorphism identifies the intrinsic cuspidality of
an actual standard Levi with the literal inside-Levi cuspidality predicate.
The semidirect decompositions and closedness proofs are arbitrary legal ones. -/
def RationalLeviCuspidalityTransportStatement : Prop :=
  DynamicLieStatement.{u} → StandardCocharacterStatement.{u} →
  ∀ (k : Type u) [Field k] [TopologicalSpace k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (_hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    ∀ (ν : cocharacterLattice T), IsGenericCocharacter i ν →
      ∀ (I : Finset (SimpleRoot i ν)),
        let L := Standard.leviScheme i ν (rootSet i ν I)
        ∀ (hL : IsConnectedReductive L),
          haveI := hL.isAffineHom
          let iL := standardLeviTorusFactor i ν (rootSet i ν I)
            (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))
          letI : TopologicalSpace (rationalPoints G) := pointTopology
          letI : TopologicalSpace (rationalPoints L) := pointTopology
          ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
            [LocallyCompactSpace (rationalPoints L)] [NonarchimedeanGroup (rationalPoints L)]
            [Fintype (SimpleRoot iL ν)]
            (hU : ∀ J, IsClosed (unipotent i ν J : Set (rationalPoints G)))
            (hUL : ∀ J, IsClosed (unipotent iL ν J : Set (rationalPoints L)))
            (hMI : IsClosed (levi i ν I : Set (rationalPoints G)))
            (hInner : ∀ K : Finset I,
              IsSemidirectDecomposition ((parabolic i ν (leviIndex I K)).subgroupOf (levi i ν I))
                ((levi i ν (leviIndex I K)).subgroupOf (levi i ν I))
                ((unipotent i ν (leviIndex I K)).subgroupOf (levi i ν I)))
            (hOwn : ∀ K, IsSemidirectDecomposition (parabolic iL ν K)
              (levi iL ν K) (unipotent iL ν K)),
            letI := hMI.locallyCompactSpace
            ∀ σ : SmoothRep.{0, u, v} ℂ (levi i ν I),
              IsCuspidal (parabolic iL ν) (levi iL ν) (unipotent iL ν) hOwn hUL
                  ((SmoothRep.pullbackFunctor (leviRationalPointHomeomorph i ν I)).obj σ) ↔
                IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU I hMI hInner σ

end Langlands.Aubert.General.RationalPointFamily
