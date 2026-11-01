import Langlands.AlgebraicGeometry.Picard.DualNumberBaseChange
import Langlands.AlgebraicGeometry.Picard.PointTangentSeparation
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-! # The topology of the actual dual-number thickening -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

variable (k : Type u) [Field k]

/-- The augmentation is a closed immersion of the actual affine schemes. -/
instance dualNumberAugmentation_isClosedImmersion :
    IsClosedImmersion (dualNumberAugmentation k) :=
  IsClosedImmersion.spec_of_surjective _ fun a ↦ ⟨TrivSqZeroExt.inl a, rfl⟩

/-- Every prime contains the square-zero augmentation kernel. -/
instance dualNumberAugmentation_surjective : Surjective (dualNumberAugmentation k) := by
  let r : DualNumber k →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom
  have hr : Function.Surjective r := fun a ↦ ⟨TrivSqZeroExt.inl a, rfl⟩
  constructor
  change Function.Surjective (PrimeSpectrum.comap r)
  rw [← Set.range_eq_univ, range_comap_of_surjective k r hr]
  apply Set.eq_univ_of_forall
  intro x a ha
  have haz : a.fst = 0 := ha
  have hn : IsNilpotent a :=
    TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst.mpr ⟨1, by simpa using haz⟩
  obtain ⟨n, hn⟩ := hn
  exact x.isPrime.mem_of_pow_mem n (hn ▸ x.asIdeal.zero_mem)

namespace DualNumberThickening

variable {k} {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- The actual base change of a scheme to the field dual numbers. -/
abbrev thickening := pullback f (dualNumberProjection k)

/-- Projection from the actual thickening to the original scheme. -/
abbrev projection : thickening f ⟶ X := pullback.fst _ _

/-- The second projection, to the actual dual-number test scheme. -/
abbrev structureMap : thickening f ⟶ Spec (CommRingCat.of (DualNumber k)) :=
  pullback.snd _ _

/-- The zero section of the actual thickening. -/
def closedPoint : X ⟶ thickening f :=
  pullback.lift (𝟙 X) (f ≫ dualNumberAugmentation k) (by
    simp [Category.assoc, dualNumberAugmentation_comp_dualNumberProjection])

@[reassoc (attr := simp)]
lemma closedPoint_projection : closedPoint f ≫ projection f = 𝟙 X :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma closedPoint_structure :
    closedPoint f ≫ structureMap f = f ≫ dualNumberAugmentation k :=
  pullback.lift_snd _ _ _

/-- The zero section is the base change of the field augmentation. -/
lemma closedPoint_isPullback :
    IsPullback (closedPoint f) f (structureMap f) (dualNumberAugmentation k) := by
  have h : IsPullback (closedPoint f ≫ projection f) f f
      (dualNumberAugmentation k ≫ dualNumberProjection k) := by
    rw [closedPoint_projection, dualNumberAugmentation_comp_dualNumberProjection]
    exact IsPullback.of_id_fst
  exact h.of_right (closedPoint_structure f)
    (IsPullback.of_hasPullback f (dualNumberProjection k))

instance closedPoint_isClosedImmersion : IsClosedImmersion (closedPoint f) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (closedPoint_isPullback f).flip inferInstance

instance closedPoint_surjective : Surjective (closedPoint f) :=
  MorphismProperty.of_isPullback (P := @Surjective)
    (closedPoint_isPullback f).flip inferInstance

@[simp]
lemma projection_closedPoint_apply (x : X) : projection f (closedPoint f x) = x := by
  rw [← Scheme.Hom.comp_apply, closedPoint_projection]
  rfl

@[simp]
lemma closedPoint_projection_apply (x : thickening f) :
    closedPoint f (projection f x) = x := by
  obtain ⟨y, rfl⟩ := (closedPoint f).surjective x
  rw [projection_closedPoint_apply]

/-- The topology of the actual thickening is the original topology.
The forward map is the actual projection and the inverse is the zero section. -/
def underlyingHomeomorph : thickening f ≃ₜ X where
  toFun := projection f
  invFun := closedPoint f
  left_inv := closedPoint_projection_apply f
  right_inv := projection_closedPoint_apply f
  continuous_toFun := (projection f).continuous
  continuous_invFun := (closedPoint f).continuous

@[simp]
lemma underlyingHomeomorph_apply (x : thickening f) :
    underlyingHomeomorph f x = projection f x := rfl

@[simp]
lemma underlyingHomeomorph_symm_apply (x : X) :
    (underlyingHomeomorph f).symm x = closedPoint f x := rfl

/-- Opens of the actual thickening correspond by inverse image under the projection. -/
def opensEquiv : X.Opens ≃o (thickening f).Opens :=
  (underlyingHomeomorph f).symm.opensCongr

@[simp]
lemma mem_opensEquiv (U : X.Opens) (x : thickening f) :
    x ∈ opensEquiv f U ↔ projection f x ∈ U := Iff.rfl

@[simp]
lemma mem_opensEquiv_symm (V : (thickening f).Opens) (x : X) :
    x ∈ (opensEquiv f).symm V ↔ closedPoint f x ∈ V := Iff.rfl

end DualNumberThickening

end Langlands.AlgebraicGeometry.Picard
