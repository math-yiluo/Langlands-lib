import Langlands.AlgebraicGeometry.PointTopology.SchemeCoefficientStatements
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeCoefficientProofs
import Langlands.AlgebraicGeometry.PointTopology.SchemeOpenPointProofs

/-! # Coefficient continuity and openness for actual scheme points -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]

/-- Coefficient change commutes with the actual inclusion of an open subscheme. -/
theorem changeRing_openPointMap
    (X : Over (Spec (CommRingCat.of R))) (U : X.left.Opens) (f : S →ₐ[R] T) :
    RingPoint.changeRing (X := X) f ∘ openPointMap R X S U =
      openPointMap R X T U ∘ RingPoint.changeRing (X := openOver R X U) f := by
  funext p
  exact (Category.assoc _ _ _).symm

variable [TopologicalSpace S] [TopologicalSpace T]

/-- The defining final topology reduces coefficient continuity to affine charts. -/
theorem schemeCoefficientContinuity_proof :
    SchemeCoefficientContinuityProperty R S T := by
  intro X f hf
  let : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
  let : TopologicalSpace (RingPoint R X T) := schemePointTopology R X T
  change Continuous (RingPoint.changeRing (X := X) f)
  refine ⟨?_⟩
  intro W hW
  apply (schemePointTopology_isOpen_iff R X S _).mpr
  intro U
  let : IsAffine (openOver R X U.val).left := U.property
  have hc := (schemePointTopology_continuous_chart R X T U).comp
    (affineSchemeCoefficientContinuity_proof R S T (openOver R X U.val) f hf)
  change IsOpen ((RingPoint.changeRing (X := X) f ∘ openPointMap R X S U.val) ⁻¹' W)
  rw [changeRing_openPointMap R S T X U.val f]
  exact hc.isOpen_preimage W hW

/-- Images of open sets are unions of open images from affine charts of the source. -/
theorem schemeCoefficientOpen_proof
    [IsLocalRing S] [IsLocalRing T] [IsTopologicalRing S] [IsTopologicalRing T]
    [IsOpenUnits T] : SchemeCoefficientOpenProperty R S T := by
  intro X _ f hf
  let : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
  let : TopologicalSpace (RingPoint R X T) := schemePointTopology R X T
  change IsOpenMap (RingPoint.changeRing (X := X) f)
  intro W hW
  apply isOpen_iff_forall_mem_open.mpr
  rintro y ⟨p, hpW, rfl⟩
  obtain ⟨U, q, hq⟩ := exists_affineOpenPoint R X S p
  let : IsAffine (openOver R X U.val).left := U.property
  let : LocallyOfFiniteType (openOver R X U.val).hom := by
    change LocallyOfFiniteType (U.val.ι ≫ X.hom)
    infer_instance
  let V := openPointMap R X S U.val ⁻¹' W
  have hV : IsOpen V := (schemePointTopology_isOpen_iff R X S W).mp hW U
  let g := RingPoint.changeRing (X := openOver R X U.val) f
  have hg : IsOpenEmbedding g :=
    affineSchemeCoefficientOpen_proof R S T (openOver R X U.val) f hf
  let B := openPointMap R X T U.val '' (g '' V)
  refine ⟨B, ?_, ?_, ?_⟩
  · rintro z ⟨r, ⟨s, hs, rfl⟩, rfl⟩
    refine ⟨openPointMap R X S U.val s, hs, ?_⟩
    exact congrFun (changeRing_openPointMap R S T X U.val f) s
  · exact (isOpenEmbedding_schemeAffineChart R T X U).isOpenMap _
      (hg.isOpenMap V hV)
  · refine ⟨g q, ⟨q, ?_, rfl⟩, ?_⟩
    · change openPointMap R X S U.val q ∈ W
      rw [hq]
      exact hpW
    · exact (congrFun (changeRing_openPointMap R S T X U.val f) q).symm.trans
        (congrArg (RingPoint.changeRing (X := X) f) hq)

/-- The coefficient properties with their separate hypotheses. -/
theorem schemeCoefficientProperties_proof : SchemeCoefficientProperties R S T := by
  refine ⟨schemeCoefficientContinuity_proof R S T, ?_⟩
  intro _ _ _ _ _
  exact schemeCoefficientOpen_proof R S T

end Langlands.AlgebraicGeometry.PointTopology
