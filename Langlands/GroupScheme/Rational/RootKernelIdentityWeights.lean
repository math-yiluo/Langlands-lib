import Langlands.GroupScheme.Rational.RootKernelIdentityAction
import Langlands.GroupScheme.Lie.SmoothDifferential
import Langlands.GroupScheme.Rational.KernelCentralizerStructureProof
import Langlands.GroupScheme.Rational.SemigroupWeightSupport

/-! # Integral weights and roots in the full-kernel identity component -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace Lie

variable {R : CommRingCat.{u}} {H C G : GroupScheme (Spec R)}
    [IsAffineHom H.X.hom] [IsAffineHom C.X.hom] [IsAffineHom G.X.hom]

/-- Differentiation of actual group homomorphisms respects composition. -/
theorem targetMapLinear_comp (f : H ⟶ C) (g : C ⟶ G)
    (A : Type u) [CommRing A] [Algebra R A] :
    targetMapLinear (f ≫ g) A =
      (targetMapLinear g A).comp (targetMapLinear f A) := by
  apply LinearMap.ext
  intro X
  apply Additive.toMul.injective
  apply Subtype.ext
  exact (Category.assoc _ _ _).symm

end Lie

namespace IdentityComponent

variable {k : Type u} [Field k]
    {C G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth C.X.hom] [IsAffineHom C.X.hom] [IsAffineHom G.X.hom]

-- Expose the existing structures explicitly through the identity-component abbreviation.
local instance (A : Type u) [CommRing A] [Algebra k A] :
    CommGroup (lieKernel (identityComponent C) A) :=
  lieKernelCommGroup (identityComponent C)

local instance (A : Type u) [CommRing A] [Algebra k A] :
    Module A (Additive (lieKernel (identityComponent C) A)) :=
  lieKernelModule (identityComponent C)

/-- Passing to the actual identity component preserves the ambient differential
range over every coefficient algebra. -/
theorem range_targetMapLinear_comp (j : C ⟶ G)
    (A : Type u) [CommRing A] [Algebra k A] :
    (Lie.targetMapLinear (identityComponentι C ≫ j) A).range =
      LinearMap.range (Lie.targetMapLinear j A) := by
  rw [Lie.targetMapLinear_comp]
  apply LinearMap.range_comp_of_range_eq_top
  apply LinearMap.range_eq_top.mpr
  exact Lie.targetMapLinear_surjective_of_smooth (identityComponentι C) A inferInstance

end IdentityComponent

namespace RelativeRoot

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G C : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [Smooth C.X.hom] [IsAffineHom C.X.hom]
    (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    (a : characterLattice T) (j : C ⟶ G)
    (hj : (kernelCentralizer i a).IsRepresentedBy j)

-- Expose the existing structures explicitly through the identity-component abbreviation.
local instance (A : Type u) [CommRing A] [Algebra k A] :
    CommGroup (lieKernel (identityComponent C) A) :=
  lieKernelCommGroup (identityComponent C)

local instance (A : Type u) [CommRing A] [Algebra k A] :
    Module A (Additive (lieKernel (identityComponent C) A)) :=
  lieKernelModule (identityComponent C)

include hT hj in
/-- The actual identity component has the same exact integral ambient Lie image
as the represented full character-kernel centralizer. -/
theorem kernelCentralizerIdentity_hasLieImage :
    HasLieImage (SubgroupFunctor.range (identityComponentι C ≫ j))
      (integralWeightSpan i a) := by
  have : Mono j.hom.hom := hj.1
  have : Mono (identityComponentι C ≫ j).hom.hom := by
    change Mono ((identityComponentι C).hom.hom ≫ j.hom.hom)
    infer_instance
  have hC := hasLieImage_of_isRepresentedBy j hj
  have hSpan : kernelLieInvariants i a = integralWeightSpan i a :=
    le_antisymm (kernelLieInvariants_le_integralWeightSpan G T hT i a)
      (integralWeightSpan_le_kernelLieInvariants i a)
  have hFull : HasLieImage (kernelCentralizer i a) (integralWeightSpan i a) := by
    rw [← hSpan]
    exact kernelCentralizer_hasLieImage i a
  have hrange : LinearMap.range (Lie.targetMapLinear j k) = integralWeightSpan i a :=
    HasLieImage.unique hC hFull
  rw [← hrange, ← IdentityComponent.range_targetMapLinear_comp j k]
  exact hasLieImage_range (identityComponentι C ≫ j)

omit [LocallyOfFiniteType G.X.hom] in
/-- The semigroup weight span on the full integral cyclic subgroup is precisely
the existing integral adjoint weight span, including its zero weight. -/
theorem semigroupWeightSpan_zmultiples :
    semigroupWeightSpan (AutomorphicAction.conjugation i)
        (AddSubgroup.zmultiples a).toAddSubmonoid.toAddSubsemigroup =
      integralWeightSpan i a := by
  apply le_antisymm
  · refine iSup_le fun χ => ?_
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp χ.property
    rw [actionWeightSpace_conjugation, ← hn]
    exact le_iSup (fun n : ℤ => weightSpace i (n • a)) n
  · refine iSup_le fun n => ?_
    have hn : n • a ∈ AddSubgroup.zmultiples a :=
      AddSubgroup.mem_zmultiples_iff.mpr ⟨n, rfl⟩
    exact le_iSup_of_le ⟨n • a, hn⟩
      (by rw [actionWeightSpace_conjugation])

/-- The inclusion maps each intrinsic component weight space onto the
intersection of the ambient weight space with the full integral Lie image. -/
theorem map_weightSpace_kernelCentralizerIdentityTorus (χ : characterLattice T) :
    (weightSpace (kernelCentralizerIdentityTorus i hT a j hj) χ).map
        (Lie.targetMapLinear (identityComponentι C ≫ j) k) =
      weightSpace i χ ⊓ integralWeightSpan i a := by
  have : Mono j.hom.hom := hj.1
  have : Mono (identityComponentι C ≫ j).hom.hom := by
    change Mono ((identityComponentι C).hom.hom ≫ j.hom.hom)
    infer_instance
  have hmap := map_actionWeightSpace_eq_inf_tangentSubmodule
    (AutomorphicAction.conjugation i) (kernelCentralizerIdentityAction i hT a j hj)
    (identityComponentι C ≫ j)
    (fun _ s x => kernelCentralizerIdentityAction_act_comp_ambient i hT a j hj s x) χ
  have hLie := (hasLieImage_iff_tangentSubmodule_eq _ _).mp
    (kernelCentralizerIdentity_hasLieImage i hT a j hj)
  simpa only [kernelCentralizerIdentityAction, actionWeightSpace_conjugation, hLie] using hmap

/-- At each integral multiple of the original character, the actual component
weight space maps onto the entire ambient weight space. -/
theorem map_weightSpace_kernelCentralizerIdentityTorus_of_mem_zmultiples
    (χ : characterLattice T) (hχ : χ ∈ AddSubgroup.zmultiples a) :
    (weightSpace (kernelCentralizerIdentityTorus i hT a j hj) χ).map
        (Lie.targetMapLinear (identityComponentι C ≫ j) k) = weightSpace i χ := by
  rw [map_weightSpace_kernelCentralizerIdentityTorus, inf_eq_left]
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hχ
  rw [← hn]
  exact le_iSup (fun n : ℤ => weightSpace i (n • a)) n

/-- The differential of the actual inclusion identifies the component and
ambient weight spaces at every integral multiple of the original character. -/
def kernelCentralizerIdentityWeightSpaceEquiv
    (χ : characterLattice T) (hχ : χ ∈ AddSubgroup.zmultiples a) :
    weightSpace (kernelCentralizerIdentityTorus i hT a j hj) χ ≃ₗ[k] weightSpace i χ := by
  have : Mono j.hom.hom := hj.1
  have : Mono (identityComponentι C ≫ j).hom.hom := by
    change Mono ((identityComponentι C).hom.hom ≫ j.hom.hom)
    infer_instance
  exact (Submodule.equivMapOfInjective (Lie.targetMapLinear (identityComponentι C ≫ j) k)
    (Lie.targetMapLinear_injective (identityComponentι C ≫ j) k)
    (weightSpace (kernelCentralizerIdentityTorus i hT a j hj) χ)).trans
      (LinearEquiv.ofEq _ _
        (map_weightSpace_kernelCentralizerIdentityTorus_of_mem_zmultiples i hT a j hj χ hχ))

@[simp] theorem kernelCentralizerIdentityWeightSpaceEquiv_coe
    (χ : characterLattice T) (hχ : χ ∈ AddSubgroup.zmultiples a)
    (X : weightSpace (kernelCentralizerIdentityTorus i hT a j hj) χ) :
    (kernelCentralizerIdentityWeightSpaceEquiv i hT a j hj χ hχ X :
      Additive (lieKernel G k)) = Lie.targetMapLinear (identityComponentι C ≫ j) k X := rfl

/-- The component has exactly the ambient nonzero weight spaces in the full
integral cyclic subgroup of the original character lattice. -/
theorem weightSpace_kernelCentralizerIdentityTorus_ne_bot_iff
    (χ : characterLattice T) :
    weightSpace (kernelCentralizerIdentityTorus i hT a j hj) χ ≠ ⊥ ↔
      χ ∈ AddSubgroup.zmultiples a ∧ weightSpace i χ ≠ ⊥ := by
  have : Mono j.hom.hom := hj.1
  have : Mono (identityComponentι C ≫ j).hom.hom := by
    change Mono ((identityComponentι C).hom.hom ≫ j.hom.hom)
    infer_instance
  have hLie : HasLieImage (SubgroupFunctor.range (identityComponentι C ≫ j))
      (semigroupWeightSpan (AutomorphicAction.conjugation i)
        (AddSubgroup.zmultiples a).toAddSubmonoid.toAddSubsemigroup) := by
    rw [semigroupWeightSpan_zmultiples]
    exact kernelCentralizerIdentity_hasLieImage i hT a j hj
  have hSource := mem_actionWeightSupport_range_iff
    (AutomorphicAction.conjugation i) (kernelCentralizerIdentityAction i hT a j hj)
    (identityComponentι C ≫ j)
    (fun _ s x => kernelCentralizerIdentityAction_act_comp_ambient i hT a j hj s x) χ
  have hSupport := HasLieImage.mem_actionWeightSupport_iff
    (AutomorphicAction.conjugation i) hT
    (AddSubgroup.zmultiples a).toAddSubmonoid.toAddSubsemigroup hLie χ
  change χ ∈ actionWeightSupport (AutomorphicAction.conjugation i)
      (SubgroupFunctor.range (identityComponentι C ≫ j)) ↔
    χ ∈ AddSubgroup.zmultiples a ∧
      actionWeightSpace (AutomorphicAction.conjugation i) χ ≠ ⊥ at hSupport
  simpa only [kernelCentralizerIdentityAction, actionWeightSpace_conjugation] using
    hSource.symm.trans hSupport

/-- Intrinsic component roots are precisely the ambient roots which are
integral multiples of the original character, with that character unchanged. -/
theorem relativeRoots_kernelCentralizerIdentityTorus :
    relativeRoots (kernelCentralizerIdentityTorus i hT a j hj) =
      relativeRoots i ∩ (AddSubgroup.zmultiples a : Set (characterLattice T)) := by
  ext χ
  rw [mem_relativeRoots, weightSpace_kernelCentralizerIdentityTorus_ne_bot_iff]
  change (χ ≠ 0 ∧ χ ∈ AddSubgroup.zmultiples a ∧ weightSpace i χ ≠ ⊥) ↔
    (χ ≠ 0 ∧ weightSpace i χ ≠ ⊥) ∧ χ ∈ AddSubgroup.zmultiples a
  tauto

/-- The original ambient root remains an actual relative root inside the
identity component of its full-kernel centralizer. -/
theorem mem_relativeRoots_kernelCentralizerIdentityTorus (ha : a ∈ relativeRoots i) :
    a ∈ relativeRoots (kernelCentralizerIdentityTorus i hT a j hj) := by
  rw [relativeRoots_kernelCentralizerIdentityTorus]
  exact ⟨ha, AddSubgroup.mem_zmultiples_iff.mpr ⟨1, one_zsmul a⟩⟩

end RelativeRoot

end Langlands.GroupScheme
