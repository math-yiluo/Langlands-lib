import Langlands.GroupScheme.ImageGenerationAppend
import Langlands.GroupScheme.ImageGenerationDominant
import Langlands.CategoryTheory.GroupObjectDescent
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Schematic images of group homomorphisms over a field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SchematicImage

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))} (f : G ⟶ H)

/-- The scheme-theoretic image with its original structure morphism. -/
def imageOver : Over (Spec (CommRingCat.of k)) :=
  Over.mk (f.hom.hom.left.imageι ≫ H.X.hom)

/-- The canonical closed immersion into the target. -/
def inclusionOver : imageOver f ⟶ H.X :=
  Over.homMk f.hom.hom.left.imageι rfl

/-- The original homomorphism with codomain restricted to its schematic image. -/
def projectionOver : G.X ⟶ imageOver f :=
  Over.homMk f.hom.hom.left.toImage (by simp [imageOver])

@[reassoc (attr := simp)]
theorem projectionOver_fac : projectionOver f ≫ inclusionOver f = f.hom.hom :=
  Over.OverMorphism.ext f.hom.hom.left.toImage_imageι

variable [IsAffineHom H.X.hom] [QuasiCompact f.hom.hom.left]

instance instSchematicImage1 : IsClosedImmersion (inclusionOver f).left :=
  inferInstanceAs (IsClosedImmersion f.hom.hom.left.imageι)

instance instSchematicImage2 : Mono (inclusionOver f) := Over.mono_of_mono_left _

instance instSchematicImage3 : IsAffineHom (imageOver f).hom :=
  inferInstanceAs (IsAffineHom (f.hom.hom.left.imageι ≫ H.X.hom))

instance instSchematicImage4 : QuasiCompact (projectionOver f).left :=
  inferInstanceAs (QuasiCompact f.hom.hom.left.toImage)

instance instSchematicImage5 : IsSchemeTheoreticallyDominant (projectionOver f).left := by
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  exact ImageGeneration.isSchemeTheoreticallyDominant_toImage f.hom.hom.left

instance instSchematicImage6 : IsSchemeTheoreticallyDominant (projectionOver f ⊗ₘ projectionOver f).left :=
  ImageGeneration.isSchemeTheoreticallyDominant_tensorHom (projectionOver f)

/-- The unit of the original source supplies the unit of its image. -/
def imageOne : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ imageOver f :=
  η[G.X] ≫ projectionOver f

omit [IsAffineHom H.X.hom] [QuasiCompact f.hom.hom.left] in
@[reassoc (attr := simp)]
theorem imageOne_fac : imageOne f ≫ inclusionOver f = η[H.X] := by
  rw [imageOne, Category.assoc, projectionOver_fac, IsMonHom.one_hom]

/-- Multiplication factors through the schematic image. -/
theorem exists_imageMul :
    ∃ m : imageOver f ⊗ imageOver f ⟶ imageOver f,
      m ≫ inclusionOver f = (inclusionOver f ⊗ₘ inclusionOver f) ≫ μ[H.X] := by
  refine exists_over_factor_of_schematic_precomp (inclusionOver f)
    (projectionOver f ⊗ₘ projectionOver f) _
    (μ[G.X] ≫ projectionOver f) ?_
  rw [Category.assoc, projectionOver_fac, IsMonHom.mul_hom,
    tensorHom_comp_tensorHom_assoc, projectionOver_fac]

/-- The actual restricted multiplication. -/
def imageMul : imageOver f ⊗ imageOver f ⟶ imageOver f :=
  Classical.choose (exists_imageMul f)

@[reassoc (attr := simp)]
theorem imageMul_fac : imageMul f ≫ inclusionOver f =
    (inclusionOver f ⊗ₘ inclusionOver f) ≫ μ[H.X] :=
  Classical.choose_spec (exists_imageMul f)

/-- Inversion factors through the schematic image. -/
theorem exists_imageInv :
    ∃ w : imageOver f ⟶ imageOver f,
      w ≫ inclusionOver f = inclusionOver f ≫ ι[H.X] := by
  refine exists_over_factor_of_schematic_precomp (inclusionOver f)
    (projectionOver f) _ (ι[G.X] ≫ projectionOver f) ?_
  rw [← Category.assoc (projectionOver f), Category.assoc (ι[G.X]), projectionOver_fac]
  exact (GrpObj.inv_hom f.hom.hom).symm

/-- The actual restricted inverse. -/
def imageInv : imageOver f ⟶ imageOver f :=
  Classical.choose (exists_imageInv f)

@[reassoc (attr := simp)]
theorem imageInv_fac : imageInv f ≫ inclusionOver f = inclusionOver f ≫ ι[H.X] :=
  Classical.choose_spec (exists_imageInv f)

instance imageGrpObj : GrpObj (imageOver f) :=
  Langlands.CategoryTheory.GroupObjectDescent.grpObjOfMono
    (inclusionOver f) (imageOne f) (imageMul f) (imageInv f)
    (imageOne_fac f) (imageMul_fac f) (imageInv_fac f)

instance instSchematicImage7 : IsMonHom (inclusionOver f) :=
  Langlands.CategoryTheory.GroupObjectDescent.isMonHom_grpObjOfMono
    (inclusionOver f) (imageOne f) (imageMul f) (imageInv f)
    (imageOne_fac f) (imageMul_fac f) (imageInv_fac f)

instance instSchematicImage8 : IsMonHom (projectionOver f) where
  one_hom := by
    apply (cancel_mono (inclusionOver f)).mp
    rw [Category.assoc, projectionOver_fac, IsMonHom.one_hom, IsMonHom.one_hom]
  mul_hom := by
    apply (cancel_mono (inclusionOver f)).mp
    rw [Category.assoc, projectionOver_fac, IsMonHom.mul_hom,
      Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc,
      projectionOver_fac]

/-- The actual schematic-image group scheme over the original field. -/
abbrev image : GroupScheme (Spec (CommRingCat.of k)) := { X := imageOver f }

/-- The closed inclusion of the schematic-image group scheme. -/
def inclusion : image f ⟶ H := Grp.homMk (inclusionOver f)

/-- The schematically dominant projection onto the schematic-image group scheme. -/
def projection : G ⟶ image f := Grp.homMk (projectionOver f)

@[reassoc (attr := simp)]
theorem projection_inclusion : projection f ≫ inclusion f = f :=
  Grp.hom_ext _ _ (projectionOver_fac f)

instance instSchematicImage9 : IsClosedImmersion (inclusion f).hom.hom.left :=
  inferInstanceAs (IsClosedImmersion (inclusionOver f).left)

instance instSchematicImage10 : IsAffineHom (image f).X.hom :=
  inferInstanceAs (IsAffineHom (imageOver f).hom)

instance instSchematicImage11 : QuasiCompact (projection f).hom.hom.left :=
  inferInstanceAs (QuasiCompact (projectionOver f).left)

instance instSchematicImage12 : IsSchemeTheoreticallyDominant (projection f).hom.hom.left :=
  inferInstanceAs (IsSchemeTheoreticallyDominant (projectionOver f).left)

end Langlands.GroupScheme.SchematicImage
