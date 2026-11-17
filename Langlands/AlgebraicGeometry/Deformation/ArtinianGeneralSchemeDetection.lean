import Langlands.AlgebraicGeometry.Deformation.ArtinianSchemeDetection
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.LocalRing.Basic

/-! # Local Artinian detection with arbitrary target schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Deformation.ArtinianDetection

set_option backward.isDefEq.respectTransparency false in
/-- Morphisms from a locally noetherian scheme to an arbitrary scheme are
detected by all local Artinian probes. -/
theorem hom_ext_general {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (f g : X ⟶ Y)
    (h : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
      (t : Spec (CommRingCat.of A) ⟶ X), t ≫ f = t ≫ g) : f = g := by
  apply Scheme.hom_ext_of_forall
  intro x
  have hfx : f x = g x := by
    obtain ⟨s⟩ : Nonempty (Spec (X.residueField x)) := inferInstance
    have e := congrArg (fun t : Spec (X.residueField x) ⟶ Y => t s)
      (h (X.residueField x) (X.fromSpecResidueField x))
    simpa only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] using e
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  let U : X.Opens := f ⁻¹ᵁ V ⊓ g ⁻¹ᵁ V
  refine ⟨U, ⟨hxV, show g x ∈ V from hfx ▸ hxV⟩, ?_⟩
  have : IsAffine V := hV
  have : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion U.ι
  rw [← f.resLE_comp_ι (U := V) (V := U) inf_le_left,
    ← g.resLE_comp_ι (U := V) (V := U) inf_le_right]
  congr 1
  apply hom_ext
  intro A _ _ _ t
  apply (cancel_mono (Scheme.Opens.ι V)).mp
  simpa only [Category.assoc, Scheme.Hom.resLE_comp_ι] using h A (t ≫ U.ι)

/-- The same probes detect morphisms in a slice category. -/
theorem over_hom_ext {S : Scheme.{u}} {X Y : Over S}
    [IsLocallyNoetherian X.left] (f g : X ⟶ Y)
    (h : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
      (t : Spec (CommRingCat.of A) ⟶ X.left), t ≫ f.left = t ≫ g.left) :
    f = g := by
  apply Over.OverMorphism.ext
  exact hom_ext_general f.left g.left h

end Langlands.AlgebraicGeometry.Deformation.ArtinianDetection
