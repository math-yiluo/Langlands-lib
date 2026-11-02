import Langlands.AlgebraicGeometry.PointTopology.SchemeTopologyUniquenessStatements
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyCharacterization

/-!
# Uniqueness from affine characterization and an actual open chart cover
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [TopologicalSpace S]

/-- An actual open affine chart cover determines the topology of all scheme points. -/
theorem schemePointTopology_eq_of_openCharts [IsLocalRing S]
    (X : Over (Spec (CommRingCat.of R))) (T : TopologicalSpace (RingPoint R X S))
    (hT : ∀ U : X.left.affineOpens,
      letI : IsAffine (openOver R X U.val).left := U.property
      @IsOpenEmbedding (RingPoint R (openOver R X U.val) S) (RingPoint R X S)
        inferInstance T (openPointMap R X S U.val)) :
    T = schemePointTopology R X S := by
  let : TopologicalSpace (RingPoint R X S) := T
  apply TopologicalSpace.ext
  funext V
  apply propext
  rw [schemePointTopology_isOpen_iff]
  constructor
  · intro h U
    let : IsAffine (openOver R X U.val).left := U.property
    exact h.preimage (hT U).continuous
  · intro h
    apply isOpen_iff_forall_mem_open.mpr
    intro p hp
    obtain ⟨U, q, hq⟩ := exists_affineOpenPoint R X S p
    let : IsAffine (openOver R X U.val).left := U.property
    refine ⟨openPointMap R X S U.val '' (openPointMap R X S U.val ⁻¹' V),
      Set.image_preimage_subset _ _, (hT U).isOpenMap _ (h U), ?_⟩
    exact ⟨q, by change openPointMap R X S U.val q ∈ V; rw [hq]; exact hp, hq⟩

/-- Restriction of all five nonaffine axioms satisfies the existing four affine axioms. -/
theorem schemePointTopologyAxioms_toAffines
    (T : SchemePointTopologyFamily R S) (hT : SchemePointTopologyAxioms R S T) :
    AffineSchemeTopologyAxioms R S (schemePointTopologyFamilyToAffines R S T) := by
  refine ⟨?_, ?_, ?_, hT.2.2.2.2⟩
  · intro X Y _ _ _ _ f
    exact hT.1 X Y f
  · intro X Y Z _ _ _ _ _ _ f g c _ _ hc
    exact hT.2.1 X Y Z f g c hc
  · intro X Y _ _ _ _ f _
    exact hT.2.2.1 X Y f

/-- Complete source-axiom uniqueness on the actual locally finite type point spaces. -/
theorem schemePointTopologyUniqueness_proof
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [TopologicalSpace S] [IsTopologicalRing S] [IsLocalRing S] [IsOpenUnits S] :
    SchemePointTopologyUniquenessProperty R S := by
  intro T hT
  have haff := affineSchemeTopology_eq_evaluation R S
    (schemePointTopologyFamilyToAffines R S T)
    (schemePointTopologyAxioms_toAffines R S T hT)
  funext X _
  apply schemePointTopology_eq_of_openCharts R S X (T X)
  intro U
  let : IsAffine (openOver R X U.val).left := U.property
  let : LocallyOfFiniteType (openOver R X U.val).hom := by
    change LocallyOfFiniteType (U.val.ι ≫ X.hom)
    infer_instance
  let : IsOpenImmersion (openOverι R X U.val).left :=
    inferInstanceAs (IsOpenImmersion U.val.ι)
  have hU : T (openOver R X U.val) =
      (inferInstance : TopologicalSpace (RingPoint R (openOver R X U.val) S)) :=
    congrArg (fun F : AffineSchemeTopologyFamily R S => F (openOver R X U.val)) haff
  have hopen := hT.2.2.2.1 (openOver R X U.val) X (openOverι R X U.val)
  change @IsOpenEmbedding (RingPoint R (openOver R X U.val) S) (RingPoint R X S)
    (T (openOver R X U.val)) (T X) (openPointMap R X S U.val) at hopen
  rw [hU] at hopen
  exact hopen

end Langlands.AlgebraicGeometry.PointTopology
