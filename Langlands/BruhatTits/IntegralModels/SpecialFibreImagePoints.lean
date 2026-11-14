import Langlands.BruhatTits.IntegralModels.SpecialFibre
import Langlands.GroupScheme.HomImage
import Langlands.GroupScheme.DominantHomFaithfullyFlat
import Langlands.GroupScheme.SplitUnipotentQuotientSection
import Langlands.GroupScheme.SplitUnipotentAffineTorsorProof
import Langlands.GroupScheme.Unipotent.PerfectFieldSplitProof

/-! # Rational lifts through special-fibre schematic images -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SchematicImage

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (f : G ⟶ H)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

/-- Restricting a homomorphism to its actual schematic image preserves its
full kernel on every test scheme. -/
theorem kernel_range_imageProjection :
    SubgroupFunctor.range (kernelι (projection f)) =
      SubgroupFunctor.range (kernelι f) := by
  have : Mono (inclusion f).hom.hom := Over.mono_of_mono_left _
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  rw [mem_range_kernelι_iff, mem_range_kernelι_iff]
  constructor
  · intro hx
    rw [← projection_inclusion f, Grp.comp_hom_hom, ← Category.assoc, hx,
      MonObj.one_comp]
  · intro hx
    apply (cancel_mono (inclusion f).hom.hom).mp
    rw [Category.assoc, ← Grp.comp_hom_hom, projection_inclusion, hx,
      MonObj.one_comp]

variable [Smooth G.X.hom] [LocallyOfFiniteType H.X.hom]

/-- The actual schematic-image projection is the represented fppf quotient
by the full kernel of the original homomorphism. -/
theorem isFppfQuotient_imageProjection :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι f))
      (projection f) := by
  let : GeometricallyReduced G.X.hom :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.geometricallyReduced_of_smooth _
  let : Smooth (image f).X.hom := HomImage.smooth_image f
  obtain ⟨hflat, hsurj⟩ := DominantHom.flat_surjective (projection f)
  exact ⟨hflat, hsurj, HomImage.locallyOfFinitePresentation_projection f,
    kernel_range_imageProjection f⟩

variable [PerfectField k]

/-- A smooth connected unipotent full kernel over a perfect field supplies
a scheme section of the projection onto the actual schematic image. -/
theorem exists_unipotentKernelImageSection
    (hkernel : Smooth (kernel f).X.hom ∧ ConnectedSpace (kernel f).X.left ∧
      IsUnipotent (kernel f)) :
    ∃ s : (image f).X ⟶ G.X, s ≫ (projection f).hom.hom = 𝟙 (image f).X := by
  let : Smooth (kernel f).X.hom := hkernel.1
  let : IsAffineHom (kernel f).X.hom :=
    HomogeneousQuotient.affine_subgroup_of_closed G (kernel f) (kernelι f)
      (inferInstanceAs (IsClosedImmersion (kernelι f).hom.hom.left))
  have hsplit : RelativeRoot.IsSplitUnipotent (kernel f) :=
    perfectFieldUnipotentSplit k (kernel f) hkernel.2.1 hkernel.2.2
  exact HomogeneousQuotient.fppf_section_of_split_unipotent_torsors G (kernel f)
      (kernelι f) splitUnipotentAffineTorsorStatement
      (inferInstanceAs (IsClosedImmersion (kernelι f).hom.hom.left)) hsplit
      (image f) (projection f) (isFppfQuotient_imageProjection f)

/-- A chosen scheme section of the actual image projection. -/
def unipotentKernelImageSection
    (hkernel : Smooth (kernel f).X.hom ∧ ConnectedSpace (kernel f).X.left ∧
      IsUnipotent (kernel f)) : (image f).X ⟶ G.X :=
  Classical.choose (exists_unipotentKernelImageSection f hkernel)

/-- The chosen scheme section is a right inverse to the actual image projection. -/
@[reassoc (attr := simp)]
theorem unipotentKernelImageSection_comp
    (hkernel : Smooth (kernel f).X.hom ∧ ConnectedSpace (kernel f).X.left ∧
      IsUnipotent (kernel f)) :
    unipotentKernelImageSection f hkernel ≫ (projection f).hom.hom =
      𝟙 (image f).X := by
  exact Classical.choose_spec (exists_unipotentKernelImageSection f hkernel)

/-- Over a perfect field, a smooth connected unipotent full kernel makes the
projection onto the actual schematic image surjective on rational points. -/
theorem rationalPoints_imageProjection_surjective_of_unipotent_kernel
    (hkernel : Smooth (kernel f).X.hom ∧ ConnectedSpace (kernel f).X.left ∧
      IsUnipotent (kernel f)) :
    Function.Surjective (rationalPoints.map (projection f)) := by
  intro y
  refine ⟨y ≫ unipotentKernelImageSection f hkernel, ?_⟩
  change (y ≫ unipotentKernelImageSection f hkernel) ≫ (projection f).hom.hom = y
  rw [Category.assoc, unipotentKernelImageSection_comp, Category.comp_id]

end Langlands.GroupScheme.SchematicImage

namespace Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom

open Langlands.GroupScheme

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  [PerfectField (IsLocalRing.ResidueField R)]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  {source target : RelativeComponentModelData R K G}
  (φ : RelativeComponentModelHom source target)

local instance sourceSpecialFibreAffine : IsAffineHom source.neutral.specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd source.neutral.group.X.hom
    (IntegralModel.residueBaseMap R))
  infer_instance

local instance targetSpecialFibreAffine : IsAffineHom target.neutral.specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd target.neutral.group.X.hom
    (IntegralModel.residueBaseMap R))
  infer_instance

local instance sourceSpecialFibreSmooth : Smooth source.neutral.specialFibre.X.hom := by
  let : Smooth source.neutral.group.X.hom := source.neutral_smooth
  change Smooth (CategoryTheory.Limits.pullback.snd source.neutral.group.X.hom
    (IntegralModel.residueBaseMap R))
  infer_instance

local instance targetSpecialFibreFiniteType :
    LocallyOfFiniteType target.neutral.specialFibre.X.hom := by
  change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd target.neutral.group.X.hom
    (IntegralModel.residueBaseMap R))
  infer_instance

/-- The geometric kernel clause gives exactly the rational surjectivity needed
for the reduction-preimage lifting criterion. -/
theorem specialFibreImageProjection_surjective
    (hkernel : φ.HasSmoothConnectedUnipotentKernel) :
    Function.Surjective
      (rationalPoints.map (SchematicImage.projection φ.neutralSpecialFibreMap)) :=
  SchematicImage.rationalPoints_imageProjection_surjective_of_unipotent_kernel
    φ.neutralSpecialFibreMap hkernel

end Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom
