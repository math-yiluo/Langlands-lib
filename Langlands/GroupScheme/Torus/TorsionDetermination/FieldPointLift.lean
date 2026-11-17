import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion

/-! # Lifting field-valued points through morphisms with surjective stalk maps -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.TorsionDetermination

/-- A morphism with surjective stalk maps induces bijections on residue fields. -/
theorem residueFieldMap_bijective {X Y : Scheme.{u}} (f : X ⟶ Y) [SurjectiveOnStalks f]
    (x : X) : Function.Bijective (f.residueFieldMap x) := by
  refine ⟨(f.residueFieldMap x).hom.injective, ?_⟩
  intro z
  obtain ⟨s, rfl⟩ := X.residue_surjective x z
  obtain ⟨t, rfl⟩ := f.stalkMap_surjective x s
  refine ⟨Y.residue (f x) t, ?_⟩
  rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]

/-- **Field points lift through morphisms with surjective stalk maps** (for instance
immersions): a morphism `Spec F ⟶ Y` from the spectrum of a field whose point lies in the
image of `f : X ⟶ Y` factors through `f`. -/
theorem exists_lift_of_mem_range {X Y : Scheme.{u}} (f : X ⟶ Y) [SurjectiveOnStalks f]
    {F : Type u} [Field F] (p : Spec (CommRingCat.of F) ⟶ Y) {x : X}
    (hx : f x = p (IsLocalRing.closedPoint F)) :
    ∃ q : Spec (CommRingCat.of F) ⟶ X, q ≫ f = p := by
  let φ := Y.descResidueField (Scheme.stalkClosedPointTo p)
  have hp : Spec.map φ ≫ Y.fromSpecResidueField _ = p :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField F Y p
  let e := RingEquiv.ofBijective (f.residueFieldMap x).hom (residueFieldMap_bijective f x)
  let ψ : X.residueField x ⟶ CommRingCat.of F :=
    CommRingCat.ofHom e.symm.toRingHom ≫ (Y.residueFieldCongr hx).hom ≫ φ
  refine ⟨Spec.map ψ ≫ X.fromSpecResidueField x, ?_⟩
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    ← Category.assoc, ← Spec.map_comp]
  have hψ : f.residueFieldMap x ≫ ψ = (Y.residueFieldCongr hx).hom ≫ φ := by
    ext z
    change ((Y.residueFieldCongr hx).hom ≫ φ) (e.symm (e z)) = _
    rw [RingEquiv.symm_apply_apply]
  rw [hψ, Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField, hp]

end Langlands.GroupScheme.TorsionDetermination
