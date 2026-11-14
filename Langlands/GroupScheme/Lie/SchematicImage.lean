import Langlands.GroupScheme.HomImage
import Langlands.GroupScheme.KernelMonomorphism
import Langlands.GroupScheme.Rational.FppfQuotientSmooth
import Langlands.GroupScheme.Lie.SmoothDifferential

/-! # Lie images for homomorphisms with smooth scheme-theoretic kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000

namespace Langlands.GroupScheme

namespace SchematicImage

variable {k : Type u} [Field k]
    {H G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [IsAffineHom G.X.hom]
    [Smooth H.X.hom] [ConnectedSpace H.X.left]
    [LocallyOfFiniteType G.X.hom] (f : H ⟶ G)

/-- The canonical projection is an fppf quotient by the full original
scheme-theoretic kernel, including its possible infinitesimal structure. -/
theorem isFppfQuotient_projection :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι f))
      (projection f) := by
  let : GeometricallyIntegral H.X.hom :=
    smoothConnectedAffineGeometry.1 k H inferInstance inferInstance inferInstance
  refine ⟨HomImage.flat_projection f, HomImage.surjective_projection f,
    HomImage.locallyOfFinitePresentation_projection f, ?_⟩
  let : Mono (inclusion f).hom.hom := Over.mono_of_mono_left _
  exact (range_kernelι_comp_mono (projection f) (inclusion f)).symm.trans
    (congrArg (fun q : H ⟶ G => SubgroupFunctor.range (kernelι q))
      (projection_inclusion f))

/-- Smoothness of the original full kernel makes the canonical image
projection smooth. Smoothness of the image alone would not suffice. -/
theorem smooth_projection_of_smooth_kernel (hker : Smooth (kernel f).X.hom) :
    Smooth (projection f).hom.hom.left := by
  exact (isFppfQuotient_projection f).smooth_of_smooth_kernel
    (⟨inferInstance, rfl⟩ :
      (SubgroupFunctor.range (kernelι f)).IsRepresentedBy (kernelι f)) hker

end SchematicImage

local instance {k : Type u} [Field k]
    {H G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [IsAffineHom G.X.hom]
    (f : H ⟶ G) (A : Type u) [CommRing A] [Algebra k A] :
    CommGroup (lieKernel (SchematicImage.image f) A) :=
  lieKernelCommGroup (SchematicImage.image f)

local instance {k : Type u} [Field k]
    {H G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [IsAffineHom G.X.hom]
    (f : H ⟶ G) (A : Type u) [CommRing A] [Algebra k A] :
    Module A (Additive (lieKernel (SchematicImage.image f) A)) :=
  lieKernelModule (SchematicImage.image f)

namespace Lie

variable {k : Type u} [Field k]
    {H G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [IsAffineHom G.X.hom]
    [Smooth H.X.hom] [ConnectedSpace H.X.left]
    [LocallyOfFiniteType G.X.hom] (f : H ⟶ G)

local instance : IsAffineHom (SchematicImage.image f).X.hom :=
  SchematicImage.instSchematicImage10 f

/-- With smooth full kernel, the Lie image of the original map equals
the Lie image of the closed inclusion of its actual schematic image. -/
theorem range_schematicImage_inclusion_of_smooth_kernel
    (hker : Smooth (kernel f).X.hom)
    (A : Type u) [CommRing A] [Algebra k A] :
    LinearMap.range (targetMapLinear (SchematicImage.inclusion f) A) =
      LinearMap.range (targetMapLinear f A) := by
  have hsurj := targetMapLinear_surjective_of_smooth
    (SchematicImage.projection f) A
      (SchematicImage.smooth_projection_of_smooth_kernel f hker)
  have hcomp (X : Additive (lieKernel H A)) :
      targetMapLinear (SchematicImage.inclusion f) A
          (targetMapLinear (SchematicImage.projection f) A X) =
        targetMapLinear f A X := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change (X.toMul.val ≫ (SchematicImage.projection f).hom.hom) ≫
        (SchematicImage.inclusion f).hom.hom = X.toMul.val ≫ f.hom.hom
    rw [Category.assoc, ← Grp.comp_hom_hom, SchematicImage.projection_inclusion]
  ext X
  constructor
  · rintro ⟨Y, rfl⟩
    obtain ⟨Z, rfl⟩ := hsurj Y
    exact ⟨Z, (hcomp Z).symm⟩
  · rintro ⟨Y, rfl⟩
    exact ⟨targetMapLinear (SchematicImage.projection f) A Y, hcomp Y⟩

end Lie

/-- The differential image equals the Lie algebra of the actual schematic
image whenever the full scheme-theoretic kernel is smooth. -/
def SmoothKernelSchematicLieImageStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (H G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom H.X.hom] [IsAffineHom G.X.hom]
    [Smooth H.X.hom] [ConnectedSpace H.X.left]
    [LocallyOfFiniteType G.X.hom] (f : H ⟶ G),
    Smooth (kernel f).X.hom →
    ∀ (A : Type u) [CommRing A] [Algebra k A],
      LinearMap.range (Lie.targetMapLinear (SchematicImage.inclusion f) A) =
        LinearMap.range (Lie.targetMapLinear f A)

theorem smoothKernelSchematicLieImage : SmoothKernelSchematicLieImageStatement.{u} := by
  intro k _ H G _ _ _ _ _ f hker A _ _
  exact Lie.range_schematicImage_inclusion_of_smooth_kernel f hker A

end Langlands.GroupScheme
