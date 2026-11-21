import Langlands.AlgebraicGeometry.AlgebraicSpace.ReducedClosedSubspaceProof
import Langlands.AlgebraicGeometry.NormalDominantMono
import Langlands.AlgebraicGeometry.Picard.GenericSectionSchematicClosure

/-! # The schematic image of an integral dense factor of a monomorphism -/

set_option autoImplicit false

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

namespace Langlands.AlgebraicGeometry

/-- If a morphism from a reduced scheme factors through the schematic image after
precomposition by a dominant morphism, then it already factors through that image. -/
theorem exists_lift_through_image_of_dominant {Z X S S' : Scheme.{u}}
    (a : Z ⟶ X) (s : S ⟶ X) [IsReduced S] (d : S' ⟶ S) [IsDominant d]
    (b : S' ⟶ Z) (h : b ≫ a = d ≫ s) :
    ∃ t : S ⟶ a.image, t ≫ a.imageι = s := by
  apply AlgebraicSpace.ReducedClosedSubspace.exists_lift_isClosedImmersion a.imageι s
  have hclosed : IsClosed (s ⁻¹' Set.range a.imageι) :=
    a.imageι.isClosedEmbedding.isClosed_range.preimage s.continuous
  have hrange : Set.range d ⊆ s ⁻¹' Set.range a.imageι := by
    rintro _ ⟨x, rfl⟩
    refine ⟨(b ≫ a.toImage) x, ?_⟩
    change ((b ≫ a.toImage) ≫ a.imageι) x = (d ≫ s) x
    rw [Category.assoc, a.toImage_imageι, h]
  have hall := closure_minimal hrange hclosed
  rw [d.denseRange.closure_eq] at hall
  rintro _ ⟨x, rfl⟩
  exact hall (Set.mem_univ x)

variable {Z X Y : Scheme.{u}} (a : Z ⟶ X) (f : X ⟶ Y)
  [IsIntegral Z] [QuasiCompact a] [IsIntegral Y]
  [Mono f] [LocallyOfFiniteType f] [QuasiCompact f] [IsDominant (a ≫ f)]

/-- The schematic image of an integral source mapping dominantly to a normal integral
target through a quasi-compact finite-type monomorphism maps openly into that target. -/
theorem isOpenImmersion_imageι_comp (hY : HasNormalStalks Y) :
    IsOpenImmersion (a.imageι ≫ f) := by
  let := isIntegral_schematicImage a
  have : IsDominant (a.toImage ≫ (a.imageι ≫ f)) := by simpa
  have : IsDominant (a.imageι ≫ f) := IsDominant.of_comp a.toImage _
  exact isOpenImmersion_of_dominant_mono_of_hasNormalStalks _ hY

/-- The open of the target identified with the schematic image of the integral source. -/
def integralDominantImageOpen (hY : HasNormalStalks Y) : Y.Opens :=
  let := isOpenImmersion_imageι_comp a f hY
  (a.imageι ≫ f).opensRange

/-- The inclusion of the open underlying the schematic image lifts to the monomorphism. -/
def integralDominantImageOpenLift (hY : HasNormalStalks Y) :
    (integralDominantImageOpen a f hY).toScheme ⟶ X :=
  let := isOpenImmersion_imageι_comp a f hY
  (a.imageι ≫ f).isoOpensRange.inv ≫ a.imageι

@[reassoc (attr := simp)]
theorem integralDominantImageOpenLift_comp (hY : HasNormalStalks Y) :
    integralDominantImageOpenLift a f hY ≫ f = (integralDominantImageOpen a f hY).ι := by
  let := isOpenImmersion_imageι_comp a f hY
  simp [integralDominantImageOpenLift, integralDominantImageOpen, Category.assoc]

/-- A morphism to the source of the monomorphism that factors through the integral source over a
dominant test has its image in the open. -/
theorem range_comp_subset_integralDominantImageOpen {S S' : Scheme.{u}} [IsReduced S]
    (s : S ⟶ X) (d : S' ⟶ S) [IsDominant d] (b : S' ⟶ Z) (h : b ≫ a = d ≫ s)
    (hY : HasNormalStalks Y) :
    Set.range (s ≫ f) ⊆ (integralDominantImageOpen a f hY : Set Y) := by
  obtain ⟨t, ht⟩ := exists_lift_through_image_of_dominant a s d b h
  let := isOpenImmersion_imageι_comp a f hY
  change Set.range (s ≫ f) ⊆ Set.range (a.imageι ≫ f)
  rw [← ht, Category.assoc]
  exact Set.range_comp_subset_range t (a.imageι ≫ f)

end Langlands.AlgebraicGeometry
