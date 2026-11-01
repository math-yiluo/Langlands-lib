import Langlands.Representation.Geometric.FlattenedIntersectionTransport
import Langlands.Representation.Geometric.PieceGrothendieck
import Langlands.Representation.Parabolic.FlattenedGrothendieck
import Langlands.Representation.Parabolic.WholeLeviConjugacyGrothendieck

/-! Induction of actual geometric pieces on exact finite-length K0. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear SmoothRep CuspidalSupport Parabolic CategoryTheory

universe uF uV

section MiddleTransport

variable (F : Type uF) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {n : ℕ} (B C : BlockShape n) (w : Equiv.Perm (Fin n))
  (S : BlockRefinement B) (R : BlockRefinement C)
  (hS : sourceLevi F B C w = refinedLevi F B S)
  (hR : sourceLevi F C B w⁻¹ = refinedLevi F C R)

/-- The actual transport between the refined intersections preserves finite length. -/
theorem refinedIntersectionTransportFunctor_preservesFiniteLength :
    PreservesFiniteLength
      (refinedIntersectionTransportFunctor.{uF, uV} F B C w S R hS hR) :=
  (subgroupEqualityFunctor_preservesFiniteLength _ _ hS.symm).comp
    ((intersectionTransportFunctor_preservesFiniteLength F B C w).comp
      (subgroupEqualityFunctor_preservesFiniteLength _ _ hR))

/-- The same transport preserves actual short exact sequences. -/
theorem refinedIntersectionTransportFunctor_preservesShortExact :
    PreservesFiniteLengthShortExact
      (refinedIntersectionTransportFunctor.{uF, uV} F B C w S R hS hR) :=
  PreservesFiniteLengthShortExact.comp
    (subgroupEqualityFunctor_preservesFiniteLength _ _ hS.symm)
    (subgroupEqualityFunctor_preservesShortExact _ _ hS.symm)
    (PreservesFiniteLengthShortExact.comp
      (intersectionTransportFunctor_preservesFiniteLength F B C w)
      (intersectionTransportFunctor_preservesShortExact F B C w)
      (subgroupEqualityFunctor_preservesShortExact _ _ hR))

/-- Actual inverse intersection transport on the full exact finite-length K0. -/
def refinedIntersectionTransportK0 :
    SmoothRep.FiniteLengthGrothendieckGroup.{0, uF, max uF uV} ℂ
        (refinedLevi F B S) →ₗ[ℤ]
      SmoothRep.FiniteLengthGrothendieckGroup.{0, uF, max uF uV} ℂ
        (refinedLevi F C R) :=
  SmoothRep.FiniteLengthGrothendieckGroup.map
    (refinedIntersectionTransportFunctor F B C w S R hS hR)
    (refinedIntersectionTransportFunctor_preservesFiniteLength F B C w S R hS hR)
    (refinedIntersectionTransportFunctor_preservesShortExact F B C w S R hS hR)

/-- The exact map computes the class of the literal transported object. -/
theorem refinedIntersectionTransportK0_finiteLengthClass
    (A : SmoothRep.{0, uF, max uF uV} ℂ (refinedLevi F B S))
    (hA : A.HasFiniteLength)
    (hOut : ((refinedIntersectionTransportFunctor F B C w S R hS hR).obj A).HasFiniteLength) :
    refinedIntersectionTransportK0.{uF, uV} F B C w S R hS hR
        (SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation A hA) =
      SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation
        ((refinedIntersectionTransportFunctor F B C w S R hS hR).obj A) hOut :=
  SmoothRep.FiniteLengthGrothendieckGroup.map_ofRepresentation _ _ _ A hA

/-- Flattening turns actual intersection transport into whole-Levi transport,
as equality of maps on every virtual class. -/
theorem flattenedLeviK0_comp_refinedIntersectionTransportK0
    (hw : ConjugatesLevi (F := F) (B.flatten S) (C.flatten R) w) :
    (flattenedLeviK0.{uF, uV} F C R).toLinearMap.comp
        (refinedIntersectionTransportK0.{uF, uV} F B C w S R hS hR) =
      (leviTransportK0.{uF, uV} F (B.flatten S) (C.flatten R) w hw).toLinearMap.comp
        (flattenedLeviK0.{uF, uV} F B S).toLinearMap := by
  apply SmoothRep.FiniteLengthGrothendieckGroup.hom_ext_object ℂ (refinedLevi F B S)
  intro A
  let M := (refinedIntersectionTransportFunctor F B C w S R hS hR).obj A.val
  let P := SmoothRep.pullback (flattenedLeviEquivContinuous F C R) M
  let D := SmoothRep.pullback (flattenedLeviEquivContinuous F B S) A.val
  let Q := (transportFunctor (B.flatten S) (C.flatten R) w hw).obj D
  have hM : M.HasFiniteLength :=
    refinedIntersectionTransportFunctor_preservesFiniteLength
      F B C w S R hS hR A.val A.property
  have hP : P.HasFiniteLength :=
    pullbackFunctor_preservesFiniteLength (flattenedLeviEquivContinuous F C R) M hM
  have hD : D.HasFiniteLength :=
    pullbackFunctor_preservesFiniteLength (flattenedLeviEquivContinuous F B S) A.val A.property
  have hQ : Q.HasFiniteLength :=
    transportFunctor_preservesFiniteLength F (B.flatten S) (C.flatten R) w hw D hD
  change flattenedLeviK0 F C R
      (refinedIntersectionTransportK0 F B C w S R hS hR
        (SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation A.val A.property)) =
    leviTransportK0 F (B.flatten S) (C.flatten R) w hw
      (flattenedLeviK0 F B S
        (SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation A.val A.property))
  rw [refinedIntersectionTransportK0_finiteLengthClass F B C w S R hS hR
      A.val A.property hM,
    flattenedLeviK0_finiteLengthClass F C R M hM hP,
    flattenedLeviK0_finiteLengthClass F B S A.val A.property hD,
    leviTransportK0_finiteLengthClass F (B.flatten S) (C.flatten R) w hw D hD hQ]
  exact SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation_eq_of_equiv hP hQ
    (flattenedIntersectionTransportEquiv.{uF, max uF uV}
      F B C w S R hS hR hw A.val)

end MiddleTransport

section InducedPiece

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  {n : ℕ} (B C : BlockShape n) (w : Equiv.Perm (Fin n))
  (S : BlockRefinement B) (R : BlockRefinement C)
  (hS : sourceLevi F.Carrier B C w = refinedLevi F.Carrier B S)
  (hR : sourceLevi F.Carrier C B w⁻¹ = refinedLevi F.Carrier C R)

/-- The actual geometric-piece map factors through the actual middle transport. -/
theorem geometricPieceK0_eq_refinedInduction_comp_transport :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    geometricPieceK0.{uF, uV} F T B C w S R hS hR =
      (normalizedRefinedInductionK0.{uF, uV} F T C R).comp
        ((refinedIntersectionTransportK0.{uF, uV} F.Carrier B C w S R hS hR).comp
          (normalizedRefinedJacquetK0.{uF, uV} F T B S)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  apply SmoothRep.FiniteLengthGrothendieckGroup.hom_ext_object ℂ (B.Levi F.Carrier)
  intro A
  let J := (T.normalizedRefinedJacquetFunctor.{uF, max uF uV} B S).obj A.val
  let M := (refinedIntersectionTransportFunctor F.Carrier B C w S R hS hR).obj J
  let I := (T.normalizedRefinedInductionFunctor.{uF, max uF uV} C R).obj M
  have hJ : J.HasFiniteLength :=
    (normalizedRefinedFiniteLengthExactness.{uF, max uF uV} F T).2.1 n B S A.val A.property
  have hM : M.HasFiniteLength :=
    refinedIntersectionTransportFunctor_preservesFiniteLength
      F.Carrier B C w S R hS hR J hJ
  have hI : I.HasFiniteLength :=
    (normalizedRefinedFiniteLengthExactness.{uF, max uF uV} F T).1 n C R M hM
  change geometricPieceK0 F T B C w S R hS hR
      (B.finiteLengthClass F.Carrier A.val A.property) =
    normalizedRefinedInductionK0 F T C R
      (refinedIntersectionTransportK0 F.Carrier B C w S R hS hR
        (normalizedRefinedJacquetK0 F T B S
          (B.finiteLengthClass F.Carrier A.val A.property)))
  have h0 := geometricPieceK0_finiteLengthClass.{uF, uV}
    F T B C w S R hS hR A.val A.property hI
  have h1 := normalizedRefinedJacquetK0_finiteLengthClass.{uF, uV}
    F T B S A.val A.property hJ
  have h2 := refinedIntersectionTransportK0_finiteLengthClass.{uF, uV}
    F.Carrier B C w S R hS hR J hJ hM
  have h3 := normalizedRefinedInductionK0_finiteLengthClass.{uF, uV}
    F T C R M hM hI
  have h4 := congrArg (normalizedRefinedInductionK0.{uF, uV} F T C R) h2.symm
  have h5 := congrArg (fun x => normalizedRefinedInductionK0.{uF, uV} F T C R
    (refinedIntersectionTransportK0.{uF, uV} F.Carrier B C w S R hS hR x)) h1.symm
  exact h0.trans (h3.symm.trans (h4.trans h5))

/-- After induction to the ambient general linear group, a geometric piece is
exactly the source refinement's induction-after-Jacquet term, in every rank. -/
theorem normalizedInductionK0_comp_geometricPieceK0 :
    letI := T.topology
    (normalizedInductionK0.{uF, uV} F T C).comp
        (geometricPieceK0.{uF, uV} F T B C w S R hS hR) =
      (normalizedInductionK0.{uF, uV} F T B).comp
        ((normalizedRefinedInductionK0.{uF, uV} F T B S).comp
          (normalizedRefinedJacquetK0.{uF, uV} F T B S)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let hw := conjugatesLevi_flattened_intersections F.Carrier B C w S R hS hR
  have hpiece := geometricPieceK0_eq_refinedInduction_comp_transport.{uF, uV}
    F T B C w S R hS hR
  have hmiddle := flattenedLeviK0_comp_refinedIntersectionTransportK0.{uF, uV}
    F.Carrier B C w S R hS hR hw
  have hC := normalizedComposedInductionK0_eq_flattened.{uF, uV} F T C R
  have hB := normalizedComposedInductionK0_eq_flattened.{uF, uV} F T B S
  have hconj := normalizedInductionK0_comp_leviTransport.{uF, uV}
    F T (B.flatten S) (C.flatten R) w hw
  apply LinearMap.ext
  intro x
  let y := normalizedRefinedJacquetK0.{uF, uV} F T B S x
  have h0 := congrArg (normalizedInductionK0.{uF, uV} F T C)
    (LinearMap.congr_fun hpiece x)
  have h1 := LinearMap.congr_fun hC
    (refinedIntersectionTransportK0.{uF, uV} F.Carrier B C w S R hS hR y)
  have h2 := congrArg (normalizedInductionK0.{uF, uV} F T (C.flatten R))
    (LinearMap.congr_fun hmiddle y)
  have h3 := LinearMap.congr_fun hconj (flattenedLeviK0.{uF, uV} F.Carrier B S y)
  have h4 := LinearMap.congr_fun hB y
  exact h0.trans (h1.trans (h2.trans (h3.trans h4.symm)))

end InducedPiece
end Langlands.Geometric
