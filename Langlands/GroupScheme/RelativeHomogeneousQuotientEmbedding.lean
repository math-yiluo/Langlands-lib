import Langlands.GroupScheme.HomogeneousQuotientFromEmbedding

/-! # Relative homogeneous quotients retaining their ambient embeddings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotient
open Langlands.GroupScheme.HomogeneousQuotientFromEmbedding

namespace Langlands.GroupScheme.RelativeHomogeneousQuotient

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- An actual homogeneous quotient together with its monomorphic map into the
ambient scheme used to construct it. -/
structure EmbeddedHomogeneousQuotient (i : H ⟶ G) (Y : Over S) (r : G.X ⟶ Y) where
  quotient : HomogeneousQuotient i
  embedding : quotient.scheme ⟶ Y
  fac : quotient.projection ≫ embedding = r
  mono_embedding : Mono embedding.left

/-- Construct the relative homogeneous quotient while retaining the actual
monomorphic embedding and the factorization of the original ambient map. -/
def quotientEmbeddingOfMapKernel
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : H ⟶ G) (hi : IsClosedSubgroup i) (hH : Smooth H.X.hom)
    (Y : Over S) (r : G.X ⟶ Y) [IsSeparated Y.hom]
    (hker : ∀ (T : Over S) (g h : T ⟶ G.X),
      g ≫ r = h ≫ r ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T) :
    EmbeddedHomogeneousQuotient i Y r := by
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
  let Q : HomogeneousQuotient i := {
    scheme := D.scheme
    projection := D.projection
    separated := hsep
    locallyOfFiniteType := inferInstance
    quasiCompact := hqc
    smooth_projection := D.smooth_projection
    surjective_projection := D.surjective_projection
    quasiCompact_projection := QuasiCompact.of_comp D.projection.left D.scheme.hom
    fibers := fun T g h => (D.fibers T g h).trans (relation_iff i T g h) }
  exact ⟨Q, D.embedding, D.fac, D.mono_embedding⟩

end Langlands.GroupScheme.RelativeHomogeneousQuotient
