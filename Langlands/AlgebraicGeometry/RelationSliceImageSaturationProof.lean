import Langlands.AlgebraicGeometry.RelationSliceImageSaturationStatement

/-! # Saturation of the image of a slice -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

open AlgebraicSpace.AtlasRelation

/-- The image of a slice is contained in its relation-saturation image. -/
theorem range_subset_relation_slice_image {U R V : Scheme.{u}} (t s : R ⟶ U)
    (hr : IsEquivRel t s) (g : V ⟶ U) :
    Set.range g ⊆ Set.range (pullback.snd g t ≫ s) := by
  obtain ⟨a, hat, has⟩ := hr.refl V g
  let k : V ⟶ pullback g t := pullback.lift (𝟙 V) a (by simpa using hat.symm)
  have hk : k ≫ (pullback.snd g t ≫ s) = g := by
    dsimp only [k]
    rw [pullback.lift_snd_assoc, has]
  rintro _ ⟨v, rfl⟩
  exact ⟨k v, by change (k ≫ (pullback.snd g t ≫ s)) v = g v; rw [hk]⟩

/-- Following an arrow of the relation preserves membership in the slice image. -/
theorem mem_relation_slice_image_of_source_mem {U R V : Scheme.{u}} (t s : R ⟶ U)
    (hr : IsEquivRel t s) (g : V ⟶ U) (r : R)
    (hrange : t r ∈ Set.range (pullback.snd g t ≫ s)) :
    s r ∈ Set.range (pullback.snd g t ≫ s) := by
  let h : pullback g t ⟶ U := pullback.snd g t ≫ s
  let D := pullback h t
  let a : D ⟶ R := pullback.fst h t ≫ pullback.snd g t
  let b : D ⟶ R := pullback.snd h t
  have hab : a ≫ s = b ≫ t := by
    dsimp [a, b, h]
    simpa only [Category.assoc] using pullback.condition (f := h) (g := t)
  obtain ⟨c, hct, hcs⟩ := hr.trans D a b hab
  let v : D ⟶ V := pullback.fst h t ≫ pullback.fst g t
  have hvc : v ≫ g = c ≫ t := by
    rw [hct]
    dsimp [v, a]
    simp only [Category.assoc, pullback.condition]
  let k : D ⟶ pullback g t := pullback.lift v c hvc
  have hk : k ≫ h = pullback.snd h t ≫ s := by
    dsimp [k, h, b] at *
    simp only [pullback.lift_snd_assoc, hcs]
  obtain ⟨z, hz⟩ := hrange
  obtain ⟨p, hpz, hpr⟩ := Scheme.Pullback.exists_preimage_pullback (f := h) (g := t) z r hz
  refine ⟨k p, ?_⟩
  change (k ≫ h) p = s r
  rw [hk]
  simp only [Scheme.Hom.comp_apply, hpr]

/-- The associated slice image is saturated under the relation on underlying points. -/
theorem mem_relation_slice_image_iff {U R V : Scheme.{u}} (t s : R ⟶ U)
    (hr : IsEquivRel t s) (g : V ⟶ U) (r : R) :
    t r ∈ Set.range (pullback.snd g t ≫ s) ↔
      s r ∈ Set.range (pullback.snd g t ≫ s) := by
  constructor
  · exact mem_relation_slice_image_of_source_mem t s hr g r
  · intro h
    obtain ⟨σ, hσt, hσs, -⟩ := hr.exists_swap
    have ht : t (σ r) = s r := by
      change (σ ≫ t) r = s r
      rw [hσt]
    have hs : s (σ r) = t r := by
      change (σ ≫ s) r = t r
      rw [hσs]
    have h' := mem_relation_slice_image_of_source_mem t s hr g (σ r) (ht.symm ▸ h)
    simpa only [hs] using h'

/-- Images of slice maps are saturated under the relation. -/
theorem relationSliceImageSaturation : RelationSliceImageSaturationStatement.{u} := by
  intro U R t s hr V g
  exact ⟨range_subset_relation_slice_image t s hr g,
    mem_relation_slice_image_iff t s hr g⟩

end Langlands.AlgebraicGeometry
