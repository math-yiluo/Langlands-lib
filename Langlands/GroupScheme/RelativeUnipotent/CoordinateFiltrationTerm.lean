import Langlands.GroupScheme.VectorCoordinateBlock
import Langlands.GroupScheme.RepresentabilityTransfer
import Langlands.GroupScheme.CorepresentedSmooth

/-! # Represented filtration terms from supported coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Classical
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeUnipotent.CoordinateFiltrationTerm

open VectorGroup.CoordinateBlock

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} {d m : ℕ}
    (φ : (VectorGroup.groupScheme R d).X ≅ G.X)
    (I : Set (Fin d)) (σ : Fin m ≃ I)

/-- The coordinate-subspace immersion through a scheme chart. The chart need not
respect the group law. -/
def schemeInclusion : (VectorGroup.groupScheme R m).X ⟶ G.X :=
  (blockInclusion (VectorGroup.coordinates R d) I σ
    (fun _ _ f v => VectorGroup.coordinates_comp f v)).hom.hom ≫ φ.hom

instance mono_schemeInclusion : Mono (schemeInclusion φ I σ) := by
  let := mono_blockInclusion (VectorGroup.coordinates R d) I σ
    (fun _ _ f v => VectorGroup.coordinates_comp f v)
  unfold schemeInclusion
  infer_instance

/-- The scheme inclusion has precisely the points whose coordinates vanish
outside the block, on every test scheme. -/
theorem factors_iff (T : Over (Spec R)) (x : T ⟶ G.X) :
    (∃ y : T ⟶ (VectorGroup.groupScheme R m).X,
      y ≫ schemeInclusion φ I σ = x) ↔
      ∀ a : Fin d, a ∉ I →
        (VectorGroup.coordinates R d T (x ≫ φ.inv)).toAdd a = 0 := by
  constructor
  · rintro ⟨y, rfl⟩ a ha
    simp only [schemeInclusion, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, comp_blockInclusion, blockPoints_coord, dite_eq_right ha]
  · intro hx
    let y := blockRestrictionPoints (VectorGroup.coordinates R d) I σ T (x ≫ φ.inv)
    refine ⟨y, ?_⟩
    apply (cancel_mono φ.inv).1
    simp only [schemeInclusion, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [comp_blockInclusion]
    apply VectorGroup.points_ext
    intro a
    rw [blockPoints_coord]
    split_ifs with ha
    · rw [blockRestrictionPoints_coord]
      simp only [Equiv.apply_symm_apply]
    · exact (hx a ha).symm

/-- The underlying coordinate inclusion is a closed immersion. -/
theorem isClosedImmersion_schemeInclusion :
    IsClosedImmersion (schemeInclusion φ I σ).left := by
  have : IsAffineHom (VectorGroup.groupScheme R d).X.hom := by
    change IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin d) R))))
    infer_instance
  have : IsClosedImmersion
      (blockInclusion (VectorGroup.coordinates R d) I σ
        (fun _ _ f v => VectorGroup.coordinates_comp f v)).hom.hom.left :=
    isClosedSubgroup_blockInclusion (VectorGroup.coordinates R d) I σ
      (fun _ _ f v => VectorGroup.coordinates_comp f v)
  have : IsIso φ.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso φ).hom)
  unfold schemeInclusion
  change IsClosedImmersion (_ ≫ _)
  infer_instance

variable (F : SubgroupFunctor G)
    (hF : ∀ (T : Over (Spec R)) (x : T ⟶ G.X),
      x ∈ F.carrier T ↔ ∀ a : Fin d, a ∉ I →
        (VectorGroup.coordinates R d T (x ≫ φ.inv)).toAdd a = 0)

include hF

/-- Supported coordinates identify the original subgroup functor, without
requiring an additive chart for its group law. -/
theorem represents_subgroup (T : Over (Spec R)) (x : T ⟶ G.X) :
    x ∈ F.carrier T ↔ ∃ y : T ⟶ (VectorGroup.groupScheme R m).X,
      y ≫ schemeInclusion φ I σ = x :=
  (hF T x).trans (factors_iff φ I σ T x).symm

/-- The actual subgroup scheme on the coordinate-subspace scheme. -/
abbrev groupScheme : GroupScheme (Spec R) :=
  F.representingGroupScheme (schemeInclusion φ I σ)
    (represents_subgroup φ I σ F hF)

/-- The inclusion with the group law induced from the given subgroup functor. -/
def inclusion : groupScheme φ I σ F hF ⟶ G :=
  F.representingHom (schemeInclusion φ I σ)
    (represents_subgroup φ I σ F hF)

@[simp]
theorem inclusion_hom : (inclusion φ I σ F hF).hom.hom =
    schemeInclusion φ I σ :=
  F.representingHom_hom (schemeInclusion φ I σ)
    (represents_subgroup φ I σ F hF)

theorem isRepresentedBy_inclusion : F.IsRepresentedBy (inclusion φ I σ F hF) :=
  F.isRepresentedBy_representingHom (schemeInclusion φ I σ)
    (represents_subgroup φ I σ F hF)

theorem isClosedSubgroup_inclusion : IsClosedSubgroup (inclusion φ I σ F hF) := by
  unfold IsClosedSubgroup
  rw [inclusion_hom]
  exact isClosedImmersion_schemeInclusion φ I σ

/-- Smoothness follows from the actual underlying affine-space scheme. -/
theorem smooth_groupScheme : Smooth (groupScheme φ I σ F hF).X.hom := by
  change Smooth (VectorGroup.groupScheme R m).X.hom
  apply Corepresented.smooth_groupScheme_iff.mpr
  infer_instance

/-- The represented subgroup is affine over the base. -/
theorem isAffineHom_groupScheme : IsAffineHom (groupScheme φ I σ F hF).X.hom := by
  change IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin m) R))))
  infer_instance

end Langlands.GroupScheme.RelativeUnipotent.CoordinateFiltrationTerm
