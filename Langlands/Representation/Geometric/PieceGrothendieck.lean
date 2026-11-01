import Langlands.Representation.CuspidalSupport.JacquetVanishingSmoothPieces
import Langlands.Representation.Parabolic.RefinedFiniteLengthFunctorProof

/-! Actual geometric-piece maps on exact finite-length smooth K0. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear CategoryTheory SmoothRep

universe uF uV

section EqualityTransport

variable {G : Type uF} [Group G] [TopologicalSpace G]

/-- Equality relabeling preserves finite group-algebra length. -/
theorem subgroupEqualityFunctor_preservesFiniteLength
    (H K : Subgroup G) (h : H = K) :
    PreservesFiniteLength (subgroupEqualityFunctor.{uF, uV} H K h) := by
  subst K
  exact preservesFiniteLength_id

/-- Equality relabeling preserves actual short exact sequences. -/
theorem subgroupEqualityFunctor_preservesShortExact
    (H K : Subgroup G) (h : H = K) :
    PreservesFiniteLengthShortExact (subgroupEqualityFunctor.{uF, uV} H K h) := by
  subst K
  exact preservesFiniteLengthShortExact_id

end EqualityTransport

section IntersectionTransport

variable (F : Type uF) [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
  {n : ℕ} (B C : BlockShape n) (w : Equiv.Perm (Fin n))

/-- Inverse conjugation is a surjective change of acting group, so the
actual intersection transport preserves finite group-algebra length. -/
theorem intersectionTransportFunctor_preservesFiniteLength :
    PreservesFiniteLength (intersectionTransportFunctor.{uF, uV} F B C w) := by
  intro A hA
  exact (FiniteLengthAssembly.finiteLength_comp_surjective_iff A.representation
    (intersectionLeviConjugation F B C w).symm.toMonoidHom
    (intersectionLeviConjugation F B C w).symm.surjective).mp hA

/-- Intersection transport leaves the underlying linear maps unchanged. -/
theorem intersectionTransportFunctor_preservesShortExact :
    PreservesFiniteLengthShortExact
      (intersectionTransportFunctor.{uF, uV} F B C w) := by
  intro A D E f g _ _ _ h
  exact h

end IntersectionTransport

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  {n : ℕ} (B C : BlockShape n) (w : Equiv.Perm (Fin n))
  (S : BlockRefinement B) (R : BlockRefinement C)
  (hS : sourceLevi F.Carrier B C w = refinedLevi F.Carrier B S)
  (hR : sourceLevi F.Carrier C B w⁻¹ = refinedLevi F.Carrier C R)

/-- Every actual smooth geometric-piece functor preserves finite length. -/
theorem geometricPieceSmoothFunctor_preservesFiniteLength :
    letI := T.topology
    PreservesFiniteLength
      (CuspidalSupport.geometricPieceSmoothFunctor.{uF, uV} F T B C w S R hS hR) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hlJ := (Parabolic.normalizedRefinedFiniteLengthExactness.{uF, uV} F T).2.1 n B S
  have hlS := subgroupEqualityFunctor_preservesFiniteLength.{uF, uV} _ _ hS.symm
  have hlW := intersectionTransportFunctor_preservesFiniteLength.{uF, uV}
    F.Carrier B C w
  have hlR := subgroupEqualityFunctor_preservesFiniteLength.{uF, uV} _ _ hR
  have hlI := (Parabolic.normalizedRefinedFiniteLengthExactness.{uF, uV} F T).1 n C R
  simpa only [CuspidalSupport.geometricPieceSmoothFunctor,
    CuspidalSupport.geometricPieceInducingFunctor, Functor.assoc] using
      hlJ.comp (hlS.comp (hlW.comp (hlR.comp hlI)))

/-- Every actual smooth geometric-piece functor preserves the short exact
sequences needed to descend to exact finite-length K0. -/
theorem geometricPieceSmoothFunctor_preservesShortExact :
    letI := T.topology
    PreservesFiniteLengthShortExact
      (CuspidalSupport.geometricPieceSmoothFunctor.{uF, uV} F T B C w S R hS hR) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hlJ := (Parabolic.normalizedRefinedFiniteLengthExactness.{uF, uV} F T).2.1 n B S
  have hxJ := (Parabolic.normalizedRefinedFiniteLengthExactness.{uF, uV} F T).2.2.2 n B S
  have hlS := subgroupEqualityFunctor_preservesFiniteLength.{uF, uV} _ _ hS.symm
  have hxS := subgroupEqualityFunctor_preservesShortExact.{uF, uV} _ _ hS.symm
  have hlW := intersectionTransportFunctor_preservesFiniteLength.{uF, uV}
    F.Carrier B C w
  have hxW := intersectionTransportFunctor_preservesShortExact.{uF, uV}
    F.Carrier B C w
  have hlR := subgroupEqualityFunctor_preservesFiniteLength.{uF, uV} _ _ hR
  have hxR := subgroupEqualityFunctor_preservesShortExact.{uF, uV} _ _ hR
  have hxI := (Parabolic.normalizedRefinedFiniteLengthExactness.{uF, uV} F T).2.2.1 n C R
  simpa only [CuspidalSupport.geometricPieceSmoothFunctor,
    CuspidalSupport.geometricPieceInducingFunctor, Functor.assoc] using
      PreservesFiniteLengthShortExact.comp hlJ hxJ
        (PreservesFiniteLengthShortExact.comp hlS hxS
          (PreservesFiniteLengthShortExact.comp hlW hxW
            (PreservesFiniteLengthShortExact.comp hlR hxR hxI)))

/-- The integer-linear map of the actual smooth geometric piece, on saturated
exact finite-length Grothendieck groups. No preservation premise is assumed. -/
def geometricPieceK0 :
    letI := T.topology
    B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier →ₗ[ℤ]
      C.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier :=
  letI := T.topology
  FiniteLengthGrothendieckGroup.map
    (CuspidalSupport.geometricPieceSmoothFunctor.{uF, max uF uV} F T B C w S R hS hR)
    (geometricPieceSmoothFunctor_preservesFiniteLength.{uF, max uF uV}
      F T B C w S R hS hR)
    (geometricPieceSmoothFunctor_preservesShortExact.{uF, max uF uV}
      F T B C w S R hS hR)

/-- The piece map sends an actual finite-length class to the class of its
actual geometric piece, for every choice of the output length proof. -/
theorem geometricPieceK0_finiteLengthClass :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier)) (hA : A.HasFiniteLength)
      (hOut : ((CuspidalSupport.geometricPieceSmoothFunctor.{uF, max uF uV}
        F T B C w S R hS hR).obj A).HasFiniteLength),
      geometricPieceK0.{uF, uV} F T B C w S R hS hR
          (B.finiteLengthClass F.Carrier A hA) =
        C.finiteLengthClass F.Carrier
          ((CuspidalSupport.geometricPieceSmoothFunctor.{uF, max uF uV}
            F T B C w S R hS hR).obj A) hOut := by
  let := T.topology
  intro A hA _
  exact FiniteLengthGrothendieckGroup.map_ofRepresentation _ _ _ A hA

end Langlands.Geometric
