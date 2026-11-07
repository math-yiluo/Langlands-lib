import Langlands.Representation.Aubert.General.InertiaInductionCompression
import Langlands.Representation.Aubert.General.RationalLeviCuspidalityTransportProof
import Langlands.Representation.Parabolic.FlattenedTensorOccurrences

/-! # Compression transport from an actual rational Levi to its literal subgroup -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.LinearAlgebra.StableEndomorphism
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme

universe u v

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (I : Finset (SimpleRoot i ν))
  (hL : IsConnectedReductive (Standard.leviScheme i ν (rootSet i ν I)))

local instance rationalLeviCompressionAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance rationalLeviCompressionClosed :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance rationalLeviCompressionAffine :
    IsAffine (Standard.leviScheme i ν (rootSet i ν I)).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance rationalLeviCompressionTopology : TopologicalSpace (rationalPoints G) :=
  pointTopology
local instance rationalLeviCompressionSourceTopology :
    TopologicalSpace (rationalPoints (Standard.leviScheme i ν (rootSet i ν I))) :=
  pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (h : ∀ J, IsSemidirectDecomposition (parabolic i ν J) (levi i ν J) (unipotent i ν J))
  (hU : ∀ J, IsClosed (unipotent i ν J : Set (rationalPoints G)))

/-- The actual induction of a literal Levi object is isomorphic to its
induction after passage to the rational Levi and back, by the actual
same-carrier pullback isomorphism. -/
def rationalLeviInductionRoundtripIso
    (A : SmoothRep.{0, u, max u v} ℂ (levi i ν I)) :
    (normalizedInductionFunctor (h I) (hU I)).obj A ≅
      (rationalInertiaInductionFunctor
        (Standard.leviScheme i ν (rootSet i ν I)) (h I) (hU I)
        (leviRationalPointHomeomorph i ν I).symm).obj
        (SmoothRep.pullback (leviRationalPointHomeomorph i ν I) A) :=
  (normalizedInductionFunctor (h I) (hU I)).mapIso
    (SmoothRep.pullbackSymmIso (leviRationalPointHomeomorph i ν I) A).symm

variable [LocallyCompactSpace
    (rationalPoints (Standard.leviScheme i ν (rootSet i ν I)))]
  [NonarchimedeanGroup (rationalPoints (Standard.leviScheme i ν (rootSet i ν I)))]
  [Fintype (SimpleRoot (standardLeviTorusFactor i ν (rootSet i ν I)
    (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν)]
  (hUL : ∀ J, IsClosed
    (unipotent (standardLeviTorusFactor i ν (rootSet i ν I)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν J :
      Set (rationalPoints (Standard.leviScheme i ν (rootSet i ν I)))))
  (hMI : IsClosed (levi i ν I : Set (rationalPoints G)))
  (hInner : ∀ J : Finset I, IsSemidirectDecomposition
    ((parabolic i ν (leviIndex I J)).subgroupOf (levi i ν I))
    ((levi i ν (leviIndex I J)).subgroupOf (levi i ν I))
    ((unipotent i ν (leviIndex I J)).subgroupOf (levi i ν I)))
  (hOwn : ∀ J, IsSemidirectDecomposition
    (parabolic (standardLeviTorusFactor i ν (rootSet i ν I)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν J)
    (levi (standardLeviTorusFactor i ν (rootSet i ν I)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν J)
    (unipotent (standardLeviTorusFactor i ν (rootSet i ν I)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν J))
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (g : rationalPoints G)

include hL

set_option maxHeartbeats 800000 in
/-- Stability on the rational Levi's cuspidal images gives stability on the
actual normalized induction of every literal inside-Levi cuspidal object.
The implemented transport preserves each chosen stable exponent. -/
theorem literalLeviInduction_eventuallyStable_of_rationalImages
    (hDynamic : DynamicLieStatement.{u}) (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (hsource : ∀ B : SmoothRep.{0, u, max u v} ℂ
        (rationalPoints (Standard.leviScheme i ν (rootSet i ν I))),
      IsCuspidal
        (parabolic (standardLeviTorusFactor i ν (rootSet i ν I)
          (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν)
        (levi (standardLeviTorusFactor i ν (rootSet i ν I)
          (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν)
        (unipotent (standardLeviTorusFactor i ν (rootSet i ν I)
          (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν) hOwn hUL B →
      EventuallyStable (Jacquet.compressedAction
        ((rationalInertiaInductionFunctor
          (Standard.leviScheme i ν (rootSet i ν I)) (h I) (hU I)
          (leviRationalPointHomeomorph i ν I).symm).obj B).representation
        ((rationalInertiaInductionFunctor
          (Standard.leviScheme i ν (rootSet i ν I)) (h I) (hU I)
          (leviRationalPointHomeomorph i ν I).symm).obj B).isSmooth K hK g))
    (A : SmoothRep.{0, u, max u v} ℂ (levi i ν I))
    (hA : IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν)
      hU I hMI hInner A) :
    EventuallyStable (Jacquet.compressedAction
      ((normalizedInductionFunctor (h I) (hU I)).obj A).representation
      ((normalizedInductionFunctor (h I) (hU I)).obj A).isSmooth K hK g) := by
  let := hMI.locallyCompactSpace
  have hc := (rationalLeviCuspidalityTransport hDynamic hStandard
    k G hG T i hi ν hν I hL hU hUL hMI hInner hOwn A).mpr hA
  obtain ⟨b, hb, hpower⟩ := hsource
    (SmoothRep.pullback (leviRationalPointHomeomorph i ν I) A) hc
  let a := SmoothRep.equivOfIso (rationalLeviInductionRoundtripIso i ν I h hU A)
  refine ⟨b, hb, ?_⟩
  exact Jacquet.compactCompressionStablePower_of_retract _ _ _ _ K hK g
    a.toIntertwiningMap a.symm.toIntertwiningMap
    (by ext x; exact a.symm_apply_apply x) b hpower

end Langlands.Aubert.General.RationalPointFamily
