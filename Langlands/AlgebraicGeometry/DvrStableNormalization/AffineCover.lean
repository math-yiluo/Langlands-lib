import Langlands.AlgebraicGeometry.DvrStableNormalization.Powers

/-! # A finite affine cover as a single affine scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.DvrStableNormalization

variable (X : Scheme.{u}) [CompactSpace X]

/-- The disjoint union of a finite affine open cover of a quasi-compact scheme. -/
abbrev coverScheme : Scheme.{u} := ∐ X.affineCover.finiteSubcover.X

/-- The covering map from the disjoint union. -/
def coverMap : coverScheme X ⟶ X := Sigma.desc X.affineCover.finiteSubcover.f

instance isAffine_coverScheme : IsAffine (coverScheme X) := by
  have : ∀ i, IsAffine (X.affineCover.finiteSubcover.X i) := fun i =>
    Scheme.isAffine_affineCover X _
  unfold coverScheme
  infer_instance

instance smooth_coverMap : Smooth (coverMap X) := by
  have : IsZariskiLocalAtSource @Smooth :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth) (Q := RingHom.Smooth)
  exact IsZariskiLocalAtSource.sigmaDesc fun _ => inferInstance

instance surjective_coverMap : Surjective (coverMap X) := by
  constructor
  intro x
  obtain ⟨y, hy⟩ := X.affineCover.finiteSubcover.covers x
  refine ⟨Sigma.ι X.affineCover.finiteSubcover.X (X.affineCover.finiteSubcover.idx x) y, ?_⟩
  rw [← Scheme.Hom.comp_apply, coverMap, Sigma.ι_comp_desc]
  exact hy

end Langlands.AlgebraicGeometry.DvrStableNormalization
