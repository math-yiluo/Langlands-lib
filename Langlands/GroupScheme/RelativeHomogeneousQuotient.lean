import Langlands.GroupScheme.HomogeneousQuotientFromEmbedding

/-! # Relative homogeneous quotients from exact-fiber maps -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotient
open Langlands.GroupScheme.HomogeneousQuotientFromEmbedding

namespace Langlands.GroupScheme.RelativeHomogeneousQuotient

variable {S : Scheme.{u}} {G H : GroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]

/-- Over an arbitrary base, an exact-fiber map to a separated scheme constructs
the actual smooth homogeneous quotient. -/
theorem exists_quotient_of_map_kernel
    (i : H ⟶ G) (hi : IsClosedSubgroup i) (hH : Smooth H.X.hom)
    (Y : Over S) (r : G.X ⟶ Y) [IsSeparated Y.hom]
    (hker : ∀ (T : Over S) (g h : T ⟶ G.X),
      g ≫ r = h ≫ r ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T) :
    Nonempty (HomogeneousQuotient i) := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom.left := inferInstance
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  have hker' : ∀ (T : Over S) (g h : T ⟶ G.X),
      g ≫ r = h ≫ r ↔ relation (arrowSpace i) (source i) (target i) T ⟨g⟩ ⟨h⟩ := by
    intro T g h
    exact (hker T g h).trans (relation_iff i T g h).symm
  let D := schemeQuotientOfMapKernel (isEquivalenceRelation i)
    (hasSmoothProjections i hH) (inferInstance : LocallyOfFiniteType G.X.hom) Y r hker'
  let : Mono D.embedding.left := D.mono_embedding
  let : Smooth D.projection.left := D.smooth_projection
  let : Surjective D.projection.left := D.surjective_projection
  have hsep : IsSeparated D.scheme.hom := by
    rw [← Over.w D.embedding]
    infer_instance
  let : IsSeparated D.scheme.hom := hsep
  have hfp : LocallyOfFinitePresentation D.scheme.hom := by
    have : LocallyOfFinitePresentation (D.projection.left ≫ D.scheme.hom) := by
      rw [Over.w D.projection]
      infer_instance
    exact Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_surjective_flat_comp
      D.projection.left D.scheme.hom
  let : LocallyOfFinitePresentation D.scheme.hom := hfp
  have hqcomp : QuasiCompact (D.projection.left ≫ D.scheme.hom) := by
    rw [Over.w D.projection]
    infer_instance
  let : QuasiCompact (D.projection.left ≫ D.scheme.hom) := hqcomp
  have hqc : QuasiCompact D.scheme.hom := by
    constructor
    intro U hopen hcompact
    have himage :=
      (QuasiCompact.isCompact_preimage
        (f := D.projection.left ≫ D.scheme.hom) U hopen hcompact).image
          D.projection.left.continuous
    change IsCompact
      (D.projection.left '' (D.projection.left ⁻¹' (D.scheme.hom ⁻¹' U))) at himage
    rwa [Set.image_preimage_eq _ D.projection.left.surjective] at himage
  refine ⟨⟨D.scheme, D.projection, hsep, inferInstance, hqc,
    D.smooth_projection, D.surjective_projection,
    QuasiCompact.of_comp D.projection.left D.scheme.hom, ?_⟩⟩
  intro T g h
  exact (D.fibers T g h).trans (relation_iff i T g h)

/-- Choose the relative quotient from an exact-fiber map. -/
def quotientOfMapKernel
    (i : H ⟶ G) (hi : IsClosedSubgroup i) (hH : Smooth H.X.hom)
    (Y : Over S) (r : G.X ⟶ Y) [IsSeparated Y.hom]
    (hker : ∀ (T : Over S) (g h : T ⟶ G.X),
      g ≫ r = h ≫ r ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T) :
    HomogeneousQuotient i :=
  Classical.choice (exists_quotient_of_map_kernel i hi hH Y r hker)

end Langlands.GroupScheme.RelativeHomogeneousQuotient
