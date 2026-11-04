import Langlands.AlgebraicGeometry.PointTopology.FilteredRingPointOpenStatement
import Mathlib.CategoryTheory.Limits.Types.ColimitTypeFiltered

/-!
# Open stages of the actual point colimit
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) [CommRing R]
variable {J : Type u} [SmallCategory J] [IsFiltered J]
variable (F : J ⥤ CommAlgCat.{u} R) (X : Over (Spec (CommRingCat.of R)))
variable (τ : ∀ j : J, TopologicalSpace (RingPoint R X (F.obj j)))

/-- Membership in the image of one stage is detected by equality at a common
later stage, without an injectivity assumption on the transitions. -/
private theorem stage_preimage_image (i j : J) (V : Set (RingPoint R X (F.obj i))) :
    (ringPointColimitι R F X j) ⁻¹' ((ringPointColimitι R F X i) '' V) =
      ⋃ (k : J) (f : i ⟶ k) (g : j ⟶ k),
        (fun p : RingPoint R X (F.obj j) => p.changeRing (F.map g).hom) ⁻¹'
          ((fun p : RingPoint R X (F.obj i) => p.changeRing (F.map f).hom) '' V) := by
  ext q
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
  constructor
  · rintro ⟨p, hp, hpq⟩
    obtain ⟨k, f, g, h⟩ :=
      ((F ⋙ ringPointFunctor R X).ιColimitType_eq_iff_of_isFiltered p q).mp hpq
    exact ⟨k, f, g, p, hp, h⟩
  · rintro ⟨k, f, g, p, hp, hpq⟩
    exact ⟨p, hp,
      ((F ⋙ ringPointFunctor R X).ιColimitType_eq_iff_of_isFiltered p q).mpr
        ⟨k, f, g, hpq⟩⟩

private theorem stage_open
    (hT : ∀ (i j : J) (f : i ⟶ j),
      Continuous[τ i, τ j]
        (fun p : RingPoint R X (F.obj i) => p.changeRing (F.map f).hom) ∧
      @IsOpenMap _ _ (τ i) (τ j)
        (fun p : RingPoint R X (F.obj i) => p.changeRing (F.map f).hom))
    (i : J) :
    @IsOpenMap _ _ (τ i) (ringPointColimitTopology R F X τ)
      (ringPointColimitι R F X i) := by
  intro V hV
  apply (ringPointColimitTopology_isOpen_iff R F X τ _).mpr
  intro j
  rw [stage_preimage_image R F X i j V]
  let := τ j
  exact isOpen_iUnion (fun k => isOpen_iUnion (fun f => isOpen_iUnion (fun g =>
    (hT j k g).1.isOpen_preimage _ ((hT i k f).2 V hV))))

omit [IsFiltered J] in
private theorem stage_image_openEmbedding
    (hopen : ∀ i : J, @IsOpenMap _ _ (τ i) (ringPointColimitTopology R F X τ)
      (ringPointColimitι R F X i)) (i : J) :
    @IsOpenEmbedding _ _ (ringPointColimitStageImageTopology R F X τ i)
      (ringPointColimitTopology R F X τ)
      (fun p : RingPointColimitStageImage R F X i => p.val) := by
  let := τ i
  let := ringPointColimitTopology R F X τ
  let := ringPointColimitStageImageTopology R F X τ i
  have hq := ringPointColimitStageProjection_isQuotientMap R F X τ i
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact hq.continuous_iff.mpr (ringPointColimitTopology_continuous_ι R F X τ i)
  · exact Subtype.val_injective
  · intro V hV
    have h := hopen i _ (hq.continuous.isOpen_preimage V hV)
    change IsOpen ((Subtype.val ∘ ringPointColimitStageProjection R F X i) ''
      ((ringPointColimitStageProjection R F X i) ⁻¹' V)) at h
    rw [Set.image_comp, Set.image_preimage_eq V hq.surjective] at h
    exact h

private theorem stage_injective
    (hinj : ∀ (i j : J) (f : i ⟶ j), Function.Injective
      (fun p : RingPoint R X (F.obj i) => p.changeRing (F.map f).hom)) (i : J) :
    Function.Injective (ringPointColimitι R F X i) := by
  intro p q hpq
  obtain ⟨k, f, h⟩ :=
    ((F ⋙ ringPointFunctor R X).ιColimitType_eq_iff_of_isFiltered' p q).mp hpq
  exact hinj i k f h

/-- The exact source-qualified openness and stage-image assertion, including the
additional open-embedding conclusion for injective transitions. -/
theorem filteredRingPointOpenStages : FilteredRingPointOpenStages.{u} := by
  intro R _ J _ _ F X τ hT
  have hopen := stage_open R F X τ hT
  refine ⟨hopen, stage_image_openEmbedding R F X τ hopen, ?_⟩
  intro hinj i
  let := τ i
  let := ringPointColimitTopology R F X τ
  exact IsOpenEmbedding.of_continuous_injective_isOpenMap
    (ringPointColimitTopology_continuous_ι R F X τ i)
    (stage_injective R F X hinj i) (hopen i)

end Langlands.AlgebraicGeometry.PointTopology
