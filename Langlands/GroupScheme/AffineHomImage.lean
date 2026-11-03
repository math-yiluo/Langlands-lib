import Langlands.GroupScheme.ImageGenerationAppend
import Langlands.GroupScheme.ImageGenerationDominant
import Langlands.CategoryTheory.GroupObjectDescent
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Mathlib.AlgebraicGeometry.Group.Smooth

/-! # The schematic image of an affine group homomorphism over a field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AffineHomImage

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] (f : G ⟶ H)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

/-- The actual scheme-theoretic image, with its original map to the base. -/
def imageOver : Over (Spec (CommRingCat.of k)) :=
  Over.mk (f.hom.hom.left.imageι ≫ H.X.hom)

/-- The closed immersion of the scheme image into the original target. -/
def inclusionOver : imageOver f ⟶ H.X :=
  Over.homMk f.hom.hom.left.imageι rfl

/-- The original morphism with codomain restricted to its scheme image. -/
def projectionOver : G.X ⟶ imageOver f :=
  Over.homMk f.hom.hom.left.toImage (by simp [imageOver])

omit [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] in
@[reassoc (attr := simp)]
theorem projectionOver_fac : projectionOver f ≫ inclusionOver f = f.hom.hom :=
  Over.OverMorphism.ext f.hom.hom.left.toImage_imageι

instance : IsClosedImmersion (inclusionOver f).left :=
  inferInstanceAs (IsClosedImmersion f.hom.hom.left.imageι)

instance : Mono (inclusionOver f) := Over.mono_of_mono_left _

instance : IsAffineHom (imageOver f).hom :=
  inferInstanceAs (IsAffineHom (f.hom.hom.left.imageι ≫ H.X.hom))

instance : IsAffine (imageOver f).left := isAffine_of_isAffineHom (imageOver f).hom

instance : QuasiCompact (projectionOver f).left :=
  inferInstanceAs (QuasiCompact f.hom.hom.left.toImage)

instance : IsSchemeTheoreticallyDominant (projectionOver f).left :=
  ImageGeneration.isSchemeTheoreticallyDominant_toImage f.hom.hom.left

/-- The identity factors through the scheme image. -/
def imageOne : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ imageOver f :=
  η[G.X] ≫ projectionOver f

omit [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] in
@[reassoc (attr := simp)]
theorem imageOne_fac : imageOne f ≫ inclusionOver f = η[H.X] := by
  rw [imageOne, Category.assoc, projectionOver_fac, IsMonHom.one_hom]

/-- Multiplication factors through the scheme image. Flatness over the field
ensures that the square of the image projection remains schematically dominant. -/
theorem exists_imageMul :
    ∃ m : imageOver f ⊗ imageOver f ⟶ imageOver f,
      m ≫ inclusionOver f = (inclusionOver f ⊗ₘ inclusionOver f) ≫ μ[H.X] := by
  have : IsSchemeTheoreticallyDominant (projectionOver f ⊗ₘ projectionOver f).left :=
    ImageGeneration.isSchemeTheoreticallyDominant_tensorHom (projectionOver f)
  refine exists_over_factor_of_schematic_precomp (inclusionOver f)
    (projectionOver f ⊗ₘ projectionOver f) _
    (μ[G.X] ≫ projectionOver f) ?_
  rw [tensorHom_comp_tensorHom_assoc, projectionOver_fac, Category.assoc,
    projectionOver_fac, IsMonHom.mul_hom]

/-- Multiplication restricted to the actual scheme image. -/
def imageMul : imageOver f ⊗ imageOver f ⟶ imageOver f :=
  (exists_imageMul f).choose

@[reassoc (attr := simp)]
theorem imageMul_fac : imageMul f ≫ inclusionOver f =
    (inclusionOver f ⊗ₘ inclusionOver f) ≫ μ[H.X] :=
  (exists_imageMul f).choose_spec

/-- Inversion factors through the scheme image. -/
theorem exists_imageInv :
    ∃ w : imageOver f ⟶ imageOver f,
      w ≫ inclusionOver f = inclusionOver f ≫ ι[H.X] := by
  refine exists_over_factor_of_schematic_precomp (inclusionOver f)
    (projectionOver f) _ (ι[G.X] ≫ projectionOver f) ?_
  rw [← Category.assoc, projectionOver_fac, Category.assoc, projectionOver_fac]
  exact (GrpObj.inv_hom f.hom.hom).symm

/-- Inversion restricted to the actual scheme image. -/
def imageInv : imageOver f ⟶ imageOver f := (exists_imageInv f).choose

@[reassoc (attr := simp)]
theorem imageInv_fac : imageInv f ≫ inclusionOver f = inclusionOver f ≫ ι[H.X] :=
  (exists_imageInv f).choose_spec

instance imageGrpObj : GrpObj (imageOver f) :=
  Langlands.CategoryTheory.GroupObjectDescent.grpObjOfMono
    (inclusionOver f) (imageOne f) (imageMul f) (imageInv f)
    (imageOne_fac f) (imageMul_fac f) (imageInv_fac f)

instance : IsMonHom (inclusionOver f) :=
  Langlands.CategoryTheory.GroupObjectDescent.isMonHom_grpObjOfMono
    (inclusionOver f) (imageOne f) (imageMul f) (imageInv f)
    (imageOne_fac f) (imageMul_fac f) (imageInv_fac f)

instance : IsMonHom (projectionOver f) where
  one_hom := by
    apply (cancel_mono (inclusionOver f)).mp
    rw [Category.assoc, projectionOver_fac, IsMonHom.one_hom, IsMonHom.one_hom]
  mul_hom := by
    apply (cancel_mono (inclusionOver f)).mp
    rw [Category.assoc, projectionOver_fac, IsMonHom.mul_hom,
      Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc,
      projectionOver_fac]

/-- The affine group scheme carried by the scheme-theoretic image. -/
abbrev image : GroupScheme (Spec (CommRingCat.of k)) := { X := imageOver f }

/-- The homomorphism onto the scheme image. -/
def projection : G ⟶ image f := Grp.homMk (projectionOver f)

/-- The closed inclusion of the scheme image into the original target. -/
def inclusion : image f ⟶ H := Grp.homMk (inclusionOver f)

@[reassoc (attr := simp)]
theorem projection_inclusion : projection f ≫ inclusion f = f :=
  Grp.hom_ext _ _ (projectionOver_fac f)

instance : IsClosedImmersion (inclusion f).hom.hom.left :=
  inferInstanceAs (IsClosedImmersion (inclusionOver f).left)

instance : IsAffineHom (image f).X.hom :=
  inferInstanceAs (IsAffineHom (imageOver f).hom)

instance : IsSchemeTheoreticallyDominant (projection f).hom.hom.left :=
  inferInstanceAs (IsSchemeTheoreticallyDominant (projectionOver f).left)

instance [LocallyOfFiniteType H.X.hom] : LocallyOfFiniteType (image f).X.hom :=
  inferInstanceAs (LocallyOfFiniteType (f.hom.hom.left.imageι ≫ H.X.hom))

instance [GeometricallyReduced G.X.hom] :
    GeometricallyReduced (image f).X.hom := by
  have : GeometricallyReduced ((projectionOver f).left ≫ (imageOver f).hom) := by
    rw [Over.w]
    infer_instance
  exact ImageGeneration.geometricallyReduced_of_isSchemeTheoreticallyDominant
    (projectionOver f).left (imageOver f).hom

/-- A smooth source gives a smooth scheme image, over an arbitrary field. -/
theorem smooth_image [Smooth G.X.hom] [LocallyOfFiniteType H.X.hom] :
    Smooth (image f).X.hom := by
  have : GeometricallyReduced G.X.hom :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.geometricallyReduced_of_smooth _
  let : GrpObj (Over.mk (image f).X.hom) := inferInstanceAs (GrpObj (image f).X)
  exact smooth_of_grpObj (image f).X.hom

end Langlands.GroupScheme.AffineHomImage
