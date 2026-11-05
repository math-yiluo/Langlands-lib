import Langlands.GroupScheme.ReducedSubgroupAction
import Langlands.GroupScheme.SmoothNormalQuotient
import Langlands.GroupScheme.HomDescent
import Langlands.GroupScheme.HopfPrimitiveQuotient
import Langlands.GroupScheme.Reductive.UnipotentQuotient

/-! # Quotienting by the smooth connected core of a homomorphism kernel -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace ReducedSubgroup

variable {k : Type u} [Field k] [PerfectField k]
    {N K : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType N.X.hom] [IsAffineHom N.X.hom]
    [Smooth K.X.hom] [ConnectedSpace K.X.left]

/-- Every homomorphism from a smooth connected group factors through the reduced
identity component of its affine target. -/
def factorIdentityCore (f : K ⟶ N) : K ⟶ identityCore N := by
  let : IsReduced K.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k K.X.left K.X.hom
  exact IdentityComponent.factor (reducedSubgroup N) (liftHom f)

@[reassoc (attr := simp)]
theorem factorIdentityCore_comp (f : K ⟶ N) :
    factorIdentityCore f ≫ identityCoreι N = f := by
  let : IsReduced K.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k K.X.left K.X.hom
  simp [factorIdentityCore, identityCoreι]

end ReducedSubgroup

namespace KernelCoreQuotient

variable {k : Type u} [Field k] [PerfectField k]
    {G A : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [IsSeparated A.X.hom]
    (f : G ⟶ A)

local instance kernel_locallyOfFiniteType : LocallyOfFiniteType (kernel f).X.hom := by
  rw [← Over.w (kernelι f).hom.hom]
  infer_instance

local instance kernel_isAffineHom : IsAffineHom (kernel f).X.hom := by
  rw [← Over.w (kernelι f).hom.hom]
  infer_instance

/-- The actual smooth connected core of the scheme kernel of `f`. -/
abbrev core : GroupScheme (Spec (CommRingCat.of k)) :=
  ReducedSubgroup.identityCore (kernel f)

/-- The actual closed inclusion of the kernel core into the source. -/
def inclusion : core f ⟶ G :=
  ReducedSubgroup.identityCoreι (kernel f) ≫ kernelι f

instance isClosedImmersion_inclusion : IsClosedImmersion (inclusion f).hom.hom.left := by
  change IsClosedImmersion
    ((ReducedSubgroup.identityCoreι (kernel f)).hom.hom.left ≫ (kernelι f).hom.hom.left)
  infer_instance

/-- The kernel core is normal on every test scheme. -/
theorem isNormal : (SubgroupFunctor.range (inclusion f)).IsNormal :=
  ReducedSubgroup.isNormal_range_identityCoreι_comp (kernelι f)
    (inferInstanceAs (IsClosedImmersion (kernelι f).hom.hom.left))
    (HopfPrimitive.isNormal_range_kernelι f)

/-- The kernel core lies in the full scheme kernel, on every test scheme. -/
theorem range_inclusion_le_kernel :
    SubgroupFunctor.range (inclusion f) ≤ SubgroupFunctor.range (kernelι f) := by
  intro T x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  exact SubgroupFunctor.mem_range.mpr
    ⟨y ≫ (ReducedSubgroup.identityCoreι (kernel f)).hom.hom, Category.assoc _ _ _⟩

/-- The core inclusion is killed by the original homomorphism. -/
@[reassoc (attr := simp)]
theorem inclusion_comp : inclusion f ≫ f = 0 := by
  apply (Grp.forget _).map_injective
  change (inclusion f).hom.hom ≫ f.hom.hom = 1
  apply (mem_range_kernelι_iff f _).mp
  apply range_inclusion_le_kernel f (core f).X
  exact SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩

/-- A nonzero homomorphism has a proper smooth connected kernel core. -/
theorem inclusion_not_isIso (hf : f ≠ 0) : ¬ IsIso (inclusion f) := by
  intro hi
  let := hi
  apply hf
  calc
    f = inv (inclusion f) ≫ (inclusion f ≫ f) := by
      rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
    _ = 0 := by rw [inclusion_comp, Limits.comp_zero]

/-- Every smooth connected subgroup killed by `f` factors through its kernel
core, with compatibility of the actual inclusions. -/
theorem exists_factor_of_comp_eq_zero
    {K : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth K.X.hom] [ConnectedSpace K.X.left]
    (j : K ⟶ G) [Mono j.hom.hom] (hj : j ≫ f = 0) :
    ∃ a : K ⟶ core f, a ≫ inclusion f = j := by
  have hle : SubgroupFunctor.range j ≤ SubgroupFunctor.range (kernelι f) := by
    intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    rw [mem_range_kernelι_iff, Category.assoc, ← Grp.comp_hom_hom, hj]
    exact MonObj.comp_one y
  obtain ⟨g, hg⟩ := SubgroupFunctor.exists_factor_of_range_le hle
  refine ⟨ReducedSubgroup.factorIdentityCore g, ?_⟩
  rw [inclusion, ReducedSubgroup.factorIdentityCore_comp_assoc, hg]

/-- The actual smooth quotient by the specified normal kernel core. -/
def quotientData : SmoothNormalQuotient (inclusion f) :=
  SmoothNormalQuotient.ofClosedNormal (inclusion f)
    (inferInstanceAs (IsClosedImmersion (inclusion f).hom.hom.left))
    inferInstance (isNormal f)

/-- The quotient group scheme by the smooth connected kernel core. -/
abbrev groupScheme : GroupScheme (Spec (CommRingCat.of k)) :=
  (quotientData f).quotient

/-- Its actual quotient projection. -/
def projection : G ⟶ groupScheme f :=
  (quotientData f).projection

instance smooth_groupScheme : Smooth (groupScheme f).X.hom :=
  (quotientData f).smooth

instance separated_groupScheme : IsSeparated (groupScheme f).X.hom :=
  (quotientData f).separated

instance locallyOfFiniteType_groupScheme : LocallyOfFiniteType (groupScheme f).X.hom :=
  (quotientData f).locallyOfFiniteType

instance quasiCompact_groupScheme : QuasiCompact (groupScheme f).X.hom :=
  (quotientData f).quasiCompact

instance smooth_projection : Smooth (projection f).hom.hom.left :=
  (quotientData f).smooth_projection

instance surjective_projection : Surjective (projection f).hom.hom.left :=
  (quotientData f).surjective_projection

instance quasiCompact_projection : QuasiCompact (projection f).hom.hom.left :=
  (quotientData f).quasiCompact_projection

instance connectedSpace_groupScheme [ConnectedSpace G.X.left] :
    ConnectedSpace (groupScheme f).X.left :=
  (quotientData f).connectedSpace

/-- The projection has precisely the kernel core as its represented fppf kernel. -/
theorem isFppfQuotient :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (inclusion f)) (projection f) :=
  (quotientData f).isFppfQuotient

/-- The original homomorphism kills the full scheme kernel of the new projection. -/
theorem kernel_projection_comp :
    kernelι (projection f) ≫ f = 0 := by
  apply (Grp.forget _).map_injective
  change (kernelι (projection f)).hom.hom ≫ f.hom.hom = 1
  apply (mem_range_kernelι_iff f _).mp
  apply range_inclusion_le_kernel f (kernel (projection f)).X
  rw [← (isFppfQuotient f).2.2.2]
  exact SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩

/-- The actual homomorphism descended through the quotient by the kernel core. -/
def factor : groupScheme f ⟶ A :=
  FpqcHomDescent.hom (projection f) f (kernel_projection_comp f)

@[reassoc (attr := simp)]
theorem projection_factor : projection f ≫ factor f = f :=
  FpqcHomDescent.fac (projection f) f (kernel_projection_comp f)

/-- The descended homomorphism is uniquely determined by its composite. -/
theorem factor_unique (g : groupScheme f ⟶ A) (hg : projection f ≫ g = f) :
    g = factor f :=
  FpqcHomDescent.unique (projection f) f (kernel_projection_comp f) g hg

/-- A nonzero homomorphism remains nonzero after descent through the kernel core. -/
theorem factor_ne_zero (hf : f ≠ 0) : factor f ≠ 0 := by
  intro h
  apply hf
  rw [← projection_factor f, h, Limits.comp_zero]

/-- Unipotence descends to the actual quotient, without an affineness premise on
that quotient. -/
theorem isUnipotent (hG : IsUnipotent G) : IsUnipotent (groupScheme f) :=
  hG.of_flat_surjective (projection f)

end KernelCoreQuotient

end Langlands.GroupScheme
