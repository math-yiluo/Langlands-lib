import Langlands.AlgebraicGeometry.AlgebraicSpace.LocalRepresentationGluing
import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Morphism properties of representations obtained over an open base cover -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace LocalRepresentation

variable {B U : Scheme.{u}} {F : Presheaf B}

/-- A global representative restricted to a base chart is the local representative. -/
def localRepresentativeIso (j : U ⟶ B) (V : Over B)
    (eV : (schemeYoneda B).obj V ≅ F) (H : Over U)
    (eH : (schemeYoneda U).obj H ≅ (Over.map j).op ⋙ F) :
    (Over.pullback j).obj V ≅ H :=
  (ULiftYoneda.fullyFaithful (Over U)).preimageIso
    (representedBaseChangeIso j V eV ≪≫ eH.symm)

/-- Properties local on the target descend from local full-slice representatives. -/
theorem property_of_local_representations
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (V : Over B) (eV : (schemeYoneda B).obj V ≅ F)
    (𝒰 : Scheme.OpenCover.{u} B) (H : ∀ i, Over (𝒰.X i))
    (e : ∀ i, (schemeYoneda (𝒰.X i)).obj (H i) ≅ (Over.map (𝒰.f i)).op ⋙ F)
    (hH : ∀ i, P (H i).hom) : P V.hom := by
  apply IsZariskiLocalAtTarget.of_openCover (P := P) 𝒰
  intro i
  let d := localRepresentativeIso (𝒰.f i) V eV (H i) (e i)
  change P ((Over.pullback (𝒰.f i)).obj V).hom
  rw [← Over.w d.hom]
  exact (MorphismProperty.cancel_left_of_respectsIso P d.hom.left (H i).hom).mpr (hH i)

/-- Affine locally finitely presented local representatives glue with both
properties on the same global structure map. -/
theorem exists_affine_representation
    (hF : Presheaf.IsSheaf (fppfTopology B) F)
    (𝒰 : Scheme.OpenCover.{u} B) (H : ∀ i, Over (𝒰.X i))
    (e : ∀ i, (schemeYoneda (𝒰.X i)).obj (H i) ≅ (Over.map (𝒰.f i)).op ⋙ F)
    (hAffine : ∀ i, IsAffineHom (H i).hom)
    (hFP : ∀ i, LocallyOfFinitePresentation (H i).hom) :
    ∃ V : Over B, Nonempty ((schemeYoneda B).obj V ≅ F) ∧
      IsAffineHom V.hom ∧ LocallyOfFinitePresentation V.hom := by
  obtain ⟨V, ⟨eV⟩⟩ := exists_representation hF 𝒰 H e
  exact ⟨V, ⟨eV⟩,
    property_of_local_representations (@IsAffineHom) V eV 𝒰 H e hAffine,
    property_of_local_representations (@LocallyOfFinitePresentation) V eV 𝒰 H e hFP⟩

end LocalRepresentation

end Langlands.AlgebraicGeometry.AlgebraicSpace
