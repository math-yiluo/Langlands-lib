import Langlands.AlgebraicGeometry.PointTopology.CompactPointStatements
import Langlands.AlgebraicGeometry.PointTopology.AffineProofs

/-!
# Compactness through finite coordinates and a finite affine cover
-/

noncomputable section

universe u v

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable [TopologicalSpace S] [IsTopologicalRing S] [T2Space S] [CompactSpace S]

private theorem compact_algebraPoints (A : Type v) [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] : CompactSpace (AlgPoint R A S) := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R A)
  exact ((AlgPoint.polynomialPointHomeomorph (R := R) (S := S) (Fin n)).isClosedEmbedding.comp
    (AlgPoint.isClosedEmbedding_precomp_of_surjective f hf)).compactSpace

theorem affineSchemeCompactness_proof : AffineSchemeCompactnessProperty R S := by
  intro X _ _
  let : CompactSpace (AlgPoint R (AffineCoordinateRing R X) S) :=
    compact_algebraPoints R S (AffineCoordinateRing R X)
  exact (affineSchemePointHomeomorph R X S).isClosedEmbedding.compactSpace

theorem schemePointCompactness_proof [IsLocalRing S] :
    SchemePointCompactnessProperty R S := by
  intro X _ _
  let : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
  obtain ⟨C, hC, hcover⟩ :=
    (isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens
      (X := X.left) (U := Set.univ)).mp ⟨isCompact_univ, isOpen_univ⟩
  have hc : ∀ U : X.left.affineOpens,
      IsCompact (Set.range (openPointMap R X S U.val)) := by
    intro U
    let : IsAffine (openOver R X U.val).left := U.property
    let : LocallyOfFiniteType (openOver R X U.val).hom := by
      change LocallyOfFiniteType (U.val.ι ≫ X.hom)
      infer_instance
    let : CompactSpace (RingPoint R (openOver R X U.val) S) :=
      affineSchemeCompactness_proof R S (openOver R X U.val)
    exact isCompact_range (schemePointTopology_continuous_chart R X S U)
  have hr : (Set.univ : Set (RingPoint R X S)) =
      ⋃ U ∈ C, Set.range (openPointMap R X S U.val) := by
    ext p
    constructor
    · intro _
      have hp : p.left (IsLocalRing.closedPoint S) ∈ ⋃ U ∈ C, (U : Set X.left) := by
        rw [← hcover]
        trivial
      obtain ⟨U, hU⟩ := Set.mem_iUnion.mp hp
      obtain ⟨hUC, hpU⟩ := Set.mem_iUnion.mp hU
      refine Set.mem_iUnion.mpr ⟨U, Set.mem_iUnion.mpr ⟨hUC, ?_⟩⟩
      exact ⟨openPointLift R X S U.val p
        ((range_subset_open_iff_closedPoint R X S U.val p).mpr hpU),
        openPointMap_lift R X S U.val p _⟩
    · intro _
      trivial
  constructor
  rw [hr]
  exact hC.isCompact_biUnion (fun U _ => hc U)

theorem compactValueRingPointProperties_proof : CompactValueRingPointProperties R S := by
  refine ⟨affineSchemeCompactness_proof R S, ?_⟩
  intro _
  exact schemePointCompactness_proof R S

end Langlands.AlgebraicGeometry.PointTopology
