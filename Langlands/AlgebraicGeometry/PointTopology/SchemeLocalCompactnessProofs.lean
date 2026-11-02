import Langlands.AlgebraicGeometry.PointTopology.SchemeOpenPointProofs
import Langlands.AlgebraicGeometry.PointTopology.SchemeLocalCompactnessStatements
import Langlands.AlgebraicGeometry.PointTopology.AffineProofs

/-!
# Local compactness through the actual open affine charts
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable [TopologicalSpace S] [IsLocalRing S] [ContinuousMul S] [IsOpenUnits S]

/-- Local compactness for actual points of every locally finite type relative scheme. -/
theorem schemePointLocalCompactness_proof
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [TopologicalSpace S] [IsLocalRing S] [IsTopologicalRing S] [IsOpenUnits S]
    [T2Space S] [LocallyCompactSpace S] :
    SchemePointLocalCompactnessProperty R S := by
  intro X _
  let : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
  refine ⟨?_⟩
  intro p n hn
  obtain ⟨U, q, hq⟩ := exists_affineOpenPoint R X S p
  let : IsAffine (openOver R X U.val).left := U.property
  let : LocallyOfFiniteType (openOver R X U.val).hom := by
    change LocallyOfFiniteType (U.val.ι ≫ X.hom)
    infer_instance
  let : LocallyCompactSpace
      (AlgPoint R (AffineCoordinateRing R (openOver R X U.val)) S) :=
    affineLocalCompactness_proof R (AffineCoordinateRing R (openOver R X U.val)) S inferInstance
  let : LocallyCompactSpace (RingPoint R (openOver R X U.val) S) :=
    (affineSchemePointHomeomorph R (openOver R X U.val) S).isClosedEmbedding.locallyCompactSpace
  have hc := isOpenEmbedding_schemeAffineChart R S X U
  have hnq : n ∈ 𝓝 (openPointMap R X S U.val q) := hq.symm ▸ hn
  obtain ⟨K, hKq, hKn, hKc⟩ := local_compact_nhds (hc.continuous.continuousAt hnq)
  refine ⟨openPointMap R X S U.val '' K, ?_, Set.image_subset_iff.mpr hKn,
    hKc.image hc.continuous⟩
  simpa only [hq] using hc.isOpenMap.image_mem_nhds hKq

end Langlands.AlgebraicGeometry.PointTopology
