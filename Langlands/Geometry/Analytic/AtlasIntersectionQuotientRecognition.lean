import Langlands.Geometry.Analytic.AtlasIntersectionFiniteRecognition
import Langlands.Geometry.Analytic.GeneralizedAffinoid.ClosedQuotient

/-! # Tensor admissibility and full intersections from a recognized quotient -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.AffinoidCoproduct

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B Q : PresentedAffinoidAlgebra K}

/-- An admissible quotient of the actual coproduct induces an admissible
map from the genuine completed tensor, with the same original input legs. -/
theorem tensorLift_isAdmissibleEpi
    (q : BoundedAlgHom K (algebra K A B) Q) (hq : q.IsAdmissibleEpi) :
    (CompletedTensorAlgebra.lift (q.comp (leftMap K A B))
      (q.comp (rightMap K A B))).IsAdmissibleEpi := by
  have hq' : lift K Q A B (q.comp (leftMap K A B)) (q.comp (rightMap K A B)) = q := by
    apply hom_ext K Q A B
    · exact lift_comp_leftMap _ _ _ _ _ _
    · exact lift_comp_rightMap _ _ _ _ _ _
  rw [← lift_comp_fromCompletedTensor, hq']
  exact BoundedAlgHom.IsAdmissibleEpi.comp (fromCompletedTensor K A B) q
    (BoundedAlgHom.isAdmissibleEpi_of_bounded_section _
      (toCompletedTensor K A B) (fromCompletedTensor_comp_toCompletedTensor K A B)) hq

end Langlands.Analytic.PresentedAffinoidAlgebra.AffinoidCoproduct

namespace Langlands.Analytic.IndexedAffinoidAtlas.LocalDomain.FiniteIntersectionData

open Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}
  {U V : LocalDomain a} {Q : PresentedAffinoidAlgebra K}

/-- Finite comparison data and an admissible coproduct map yield the exact
full local-domain conclusion with its canonical bounded restrictions. -/
theorem exists_of_admissibleCoproduct
    (q : BoundedAlgHom K (AffinoidCoproduct.algebra K U.algebra V.algebra) Q)
    (d : FiniteIntersectionData U V Q
      (q.comp (AffinoidCoproduct.leftMap K U.algebra V.algebra))
      (q.comp (AffinoidCoproduct.rightMap K U.algebra V.algebra)))
    (hq : q.IsAdmissibleEpi) :
    ∃ R : LocalDomain a, ∃ hR : R.locus = U.locus ∩ V.locus,
      (CompletedTensorAlgebra.lift
        (Inclusion.ofSubset R U (by
          intro x hx
          have hx' : x ∈ U.locus ∩ V.locus := hR ▸ hx
          exact hx'.1)).restriction
        (Inclusion.ofSubset R V (by
          intro x hx
          have hx' : x ∈ U.locus ∩ V.locus := hR ▸ hx
          exact hx'.2)).restriction).IsAdmissibleEpi := by
  refine ⟨d.intersection, d.intersection_locus, ?_⟩
  exact d.tensor_isAdmissibleEpi (AffinoidCoproduct.tensorLift_isAdmissibleEpi q hq)

section ClosedQuotient

variable (J : Ideal (AffinoidCoproduct.algebra K U.algebra V.algebra))
    [IsClosed (J : Set (AffinoidCoproduct.algebra K U.algebra V.algebra))]
    (d : FiniteIntersectionData U V
      (ClosedQuotient.algebra (AffinoidCoproduct.algebra K U.algebra V.algebra) J)
      ((ClosedQuotient.map (AffinoidCoproduct.algebra K U.algebra V.algebra) J).comp
        (AffinoidCoproduct.leftMap K U.algebra V.algebra))
      ((ClosedQuotient.map (AffinoidCoproduct.algebra K U.algebra V.algebra) J).comp
        (AffinoidCoproduct.rightMap K U.algebra V.algebra)))

/-- The full local domain constructed from finite comparisons for an actual
closed coproduct quotient, retaining exactly that quotient algebra. -/
def closedCoproductIntersection : LocalDomain a := d.intersection

include d in
/-- The actual closed quotient supplies admissibility, so finite comparisons
are the only additional input needed for the full geometric conclusion. -/
theorem exists_of_closedCoproductQuotient :
    ∃ R : LocalDomain a, ∃ hR : R.locus = U.locus ∩ V.locus,
      (CompletedTensorAlgebra.lift
        (Inclusion.ofSubset R U (by
          intro x hx
          have hx' : x ∈ U.locus ∩ V.locus := hR ▸ hx
          exact hx'.1)).restriction
        (Inclusion.ofSubset R V (by
          intro x hx
          have hx' : x ∈ U.locus ∩ V.locus := hR ▸ hx
          exact hx'.2)).restriction).IsAdmissibleEpi :=
  exists_of_admissibleCoproduct _ d (ClosedQuotient.map_isAdmissibleEpi _ _)

end ClosedQuotient
end Langlands.Analytic.IndexedAffinoidAtlas.LocalDomain.FiniteIntersectionData
