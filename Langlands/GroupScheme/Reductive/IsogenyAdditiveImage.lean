import Langlands.GroupScheme.HomImage
import Langlands.GroupScheme.Rational.AdditiveGroupQuotient
import Langlands.GroupScheme.Rational.VectorGroupCoordinates
import Langlands.GroupScheme.Lie.SmoothIsogenyDimension

/-! # The actual image of a finite homomorphism from an additive line -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HomImage

variable {k : Type u} [Field k]
    {V G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom V.X.hom] [IsAffineHom G.X.hom]
    (x : V ⟶ G) [IsFinite x.hom.hom.left]

/-- Finiteness passes to the actual schematic-image projection. -/
theorem isFinite_projection : IsFinite (SchematicImage.projection x).hom.hom.left := by
  have hfac : (SchematicImage.projection x).hom.hom.left ≫
      (SchematicImage.inclusion x).hom.hom.left = x.hom.hom.left :=
    congrArg (fun f => f.hom.hom.left) (SchematicImage.projection_inclusion x)
  have : IsFinite ((SchematicImage.projection x).hom.hom.left ≫
      (SchematicImage.inclusion x).hom.hom.left) := hfac.symm ▸ inferInstance
  exact IsFinite.of_comp (SchematicImage.projection x).hom.hom.left
    (SchematicImage.inclusion x).hom.hom.left

variable [LocallyOfFiniteType G.X.hom]

/-- A finite map from an actual additive line has an actual additive-line
schematic image over any field. Its kernel may be nonreduced. -/
theorem isVectorGroupOfDimension_image
    (hV : RelativeRoot.IsVectorGroupOfDimension V 1) :
    RelativeRoot.IsVectorGroupOfDimension (SchematicImage.image x) 1 := by
  let : Smooth V.X.hom := hV.smooth
  let : ConnectedSpace V.X.left := hV.connectedSpace
  have : GeometricallyIntegral V.X.hom :=
    smoothConnectedAffineGeometry.1 k V inferInstance inferInstance inferInstance
  let : Smooth (SchematicImage.image x).X.hom := smooth_image x
  let : Flat (SchematicImage.projection x).hom.hom.left := flat_projection x
  let : Surjective (SchematicImage.projection x).hom.hom.left := surjective_projection x
  let : IsFinite (SchematicImage.projection x).hom.hom.left := isFinite_projection x
  rcases RelativeRoot.trivial_or_isVectorGroup_of_flat_surjective
      hV (SchematicImage.projection x) with htriv | hline
  · have hpoints : ∀ (Z : Over (Spec (CommRingCat.of k)))
        (z : Z ⟶ (SchematicImage.image x).X), z = 1 := by
      intro Z z
      have hz : z ∈ (SubgroupFunctor.range (𝟙 (SchematicImage.image x))).carrier Z :=
        ⟨z, Category.comp_id z⟩
      change SubgroupFunctor.range (𝟙 (SchematicImage.image x)) = ⊥ at htriv
      rw [htriv] at hz
      exact hz
    let : Subsingleton (Additive (lieKernel (SchematicImage.image x) k)) :=
      ⟨fun a b => by
        apply Additive.toMul.injective
        apply Subtype.ext
        exact (hpoints _ a.toMul.val).trans (hpoints _ b.toMul.val).symm⟩
    have heq := Lie.finrank_kernel_eq_of_flat_locallyQuasiFinite
      (SchematicImage.projection x)
    obtain ⟨e, he⟩ := hV
    have hdim := (RelativeRoot.vectorLieCoordinates e he
      (CommAlgCat.of (CommRingCat.of k) k)).finrank_eq
    simp only [Module.finrank_zero_of_subsingleton] at heq
    simp at hdim
    omega
  · exact hline

/-- A chosen actual isomorphism from the schematic image to the standard
additive line. This does not assert that the finite projection is separable. -/
def additiveImageIso (hV : RelativeRoot.IsVectorGroupOfDimension V 1) :
    SchematicImage.image x ≅ VectorGroup.groupScheme (CommRingCat.of k) 1 :=
  (isVectorGroupOfDimension_image x hV).iso

end Langlands.GroupScheme.HomImage
