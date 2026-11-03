import Langlands.GroupScheme.HomogeneousCosetRelation
import Langlands.GroupScheme.HomogeneousQuotientStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotientEmbedding
import Langlands.AlgebraicGeometry.Morphisms.LocallyOfFinitePresentationSourceDescent

/-! # Smooth subgroup quotients from an ambient map with exact coset fibers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotient

namespace Langlands.GroupScheme.HomogeneousQuotientFromEmbedding

variable {S : Scheme.{u}} {G H : GroupScheme S} (i : H ⟶ G)

/-- The actual right-coset arrow scheme viewed as an algebraic space. -/
abbrev arrowSpace : Langlands.AlgebraicGeometry.AlgebraicSpace S :=
  (schemeToSpace S).obj (HomogeneousCosetRelation.arrows i)

/-- The source endpoint on the actual functor of points. -/
abbrev source : (arrowSpace i).presheaf ⟶ (schemeYoneda S).obj G.X :=
  (schemeYoneda S).map (HomogeneousCosetRelation.source i)

/-- The target endpoint on the actual functor of points. -/
abbrev target : (arrowSpace i).presheaf ⟶ (schemeYoneda S).obj G.X :=
  (schemeYoneda S).map (HomogeneousCosetRelation.target i)

/-- The algebraic-space relation is exactly right-coset membership on every test. -/
theorem relation_iff (T : Over S) (x y : T ⟶ G.X) :
    relation (arrowSpace i) (source i) (target i) T ⟨x⟩ ⟨y⟩ ↔
      x⁻¹ * y ∈ (SubgroupFunctor.range i).carrier T := by
  rw [← HomogeneousCosetRelation.exists_arrow_iff]
  constructor
  · rintro ⟨a, ha, hb⟩
    exact ⟨a.down, congrArg ULift.down ha, congrArg ULift.down hb⟩
  · rintro ⟨a, ha, hb⟩
    refine ⟨⟨a⟩, ?_, ?_⟩
    · apply ULift.ext
      exact ha
    · apply ULift.ext
      exact hb

/-- A monomorphic subgroup gives a monomorphic equivalence relation on all tests. -/
theorem isEquivalenceRelation [Mono i.hom.hom] :
    IsEquivalenceRelation (arrowSpace i) (source i) (target i) := by
  intro T
  constructor
  · intro a b hab
    apply ULift.ext
    exact HomogeneousCosetRelation.arrow_unique i
      (congrArg ULift.down (congrArg Prod.fst hab))
      (congrArg ULift.down (congrArg Prod.snd hab))
  · refine ⟨?_, ?_, ?_⟩
    · rintro ⟨x⟩
      rw [relation_iff]
      simp
    · rintro ⟨x⟩ ⟨y⟩ hxy
      rw [relation_iff] at hxy ⊢
      simpa using ((SubgroupFunctor.range i).carrier T).inv_mem hxy
    · rintro ⟨x⟩ ⟨y⟩ ⟨z⟩ hxy hyz
      rw [relation_iff] at hxy hyz ⊢
      simpa [mul_assoc] using ((SubgroupFunctor.range i).carrier T).mul_mem hxy hyz

/-- Smoothness of the actual subgroup gives smooth relation projections. -/
theorem hasSmoothProjections (hH : Smooth H.X.hom) :
    HasSmoothProjections (arrowSpace i) (source i) (target i) := by
  refine ⟨HomogeneousCosetRelation.arrows i, 𝟙 _, HomogeneousCosetRelation.source i,
    HomogeneousCosetRelation.target i, ?_, ?_, ?_, ?_,
    HomogeneousCosetRelation.source_smooth i hH,
    HomogeneousCosetRelation.target_smooth i hH⟩
  · change (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S)).relative
      (schemeYoneda S) (𝟙 _)
    let : MorphismProperty.RespectsIso (@Etale.{u}) :=
      Etale.etale_isStableUnderBaseChange.respectsIso
    let := MorphismProperty.RespectsIso.inverseImage (@Etale.{u}) (Over.forget S)
    apply MorphismProperty.relative.of_exists
    intro V g
    refine ⟨V, g, 𝟙 V, ?_, ?_⟩
    · simpa using IsPullback.of_id_snd (f := g)
    · change Etale (𝟙 V.left)
      infer_instance
  · change (MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)).relative
      (schemeYoneda S) (𝟙 _)
    let := MorphismProperty.RespectsIso.inverseImage (@Surjective.{u}) (Over.forget S)
    apply MorphismProperty.relative.of_exists
    intro V g
    refine ⟨V, g, 𝟙 V, ?_, ?_⟩
    · simpa using IsPullback.of_id_snd (f := g)
    · change Surjective (𝟙 V.left)
      infer_instance
  · change (𝟙 _) ≫ (schemeYoneda S).map (HomogeneousCosetRelation.source i) = _
    exact Category.id_comp _
  · change (𝟙 _) ≫ (schemeYoneda S).map (HomogeneousCosetRelation.target i) = _
    exact Category.id_comp _

/-- Exact coset fibers into a separated ambient scheme give every geometric
property of the published homogeneous quotient target. -/
theorem exists_quotient_of_map_kernel
    {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : H ⟶ G) (hi : IsClosedSubgroup i) (hH : Smooth H.X.hom)
    (Y : Over (Spec (CommRingCat.of k))) (r : G.X ⟶ Y) [IsSeparated Y.hom]
    (hker : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ r = h ≫ r ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T) :
    ∃ (Q : Over (Spec (CommRingCat.of k))) (q : G.X ⟶ Q),
      IsSeparated Q.hom ∧ LocallyOfFiniteType Q.hom ∧ QuasiCompact Q.hom ∧
      Smooth q.left ∧ Surjective q.left ∧ QuasiCompact q.left ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
        g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom.left := inferInstance
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  have hker' : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
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
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : CompactSpace D.scheme.left :=
    ⟨D.projection.left.surjective.range_eq ▸ isCompact_range D.projection.left.continuous⟩
  have hqc : QuasiCompact D.scheme.hom := inferInstance
  have hqcomp : QuasiCompact (D.projection.left ≫ D.scheme.hom) := by
    rw [Over.w D.projection]
    infer_instance
  let : QuasiCompact (D.projection.left ≫ D.scheme.hom) := hqcomp
  refine ⟨D.scheme, D.projection, hsep, inferInstance, hqc,
    D.smooth_projection, D.surjective_projection,
    QuasiCompact.of_comp D.projection.left D.scheme.hom, ?_⟩
  intro T g h
  exact (D.fibers T g h).trans (relation_iff i T g h)

/-- An actual homogeneous quotient with the complete geometric and all-test fiber data. -/
structure HomogeneousQuotient where
  scheme : Over S
  projection : G.X ⟶ scheme
  separated : IsSeparated scheme.hom
  locallyOfFiniteType : LocallyOfFiniteType scheme.hom
  quasiCompact : QuasiCompact scheme.hom
  smooth_projection : Smooth projection.left
  surjective_projection : Surjective projection.left
  quasiCompact_projection : QuasiCompact projection.left
  fibers : ∀ (T : Over S) (g h : T ⟶ G.X),
    g ≫ projection = h ≫ projection ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T

/-- Choose the actual homogeneous quotient furnished by an exact-fiber ambient map. -/
def quotientOfMapKernel
    {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : H ⟶ G) (hi : IsClosedSubgroup i) (hH : Smooth H.X.hom)
    (Y : Over (Spec (CommRingCat.of k))) (r : G.X ⟶ Y) [IsSeparated Y.hom]
    (hker : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ r = h ≫ r ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T) :
    HomogeneousQuotient i :=
  Classical.choice (by
    obtain ⟨Q, q, hsep, hft, hqc, hsm, hsurj, hqqc, hfib⟩ :=
      exists_quotient_of_map_kernel i hi hH Y r hker
    exact ⟨⟨Q, q, hsep, hft, hqc, hsm, hsurj, hqqc, hfib⟩⟩)

end Langlands.GroupScheme.HomogeneousQuotientFromEmbedding
