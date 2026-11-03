import Langlands.GroupScheme.Lie.KernelTargetMaps
import Langlands.GroupScheme.Rational.ActionWeightTransport
import Langlands.GroupScheme.Rational.TangentWeightTransport
import Langlands.GroupScheme.Dynamic.ActionFunctoriality

/-! # Equivariant functoriality of intrinsic action weights -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction.IsEquivariant

open RelativeRoot

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G K : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom K.X.hom]
    {a : AutomorphicAction S.toGrp G} {b : AutomorphicAction S.toGrp K}
    {f : G ⟶ K} (hf : a.IsEquivariant b f)

include hf

/-- The actual derivative of an equivariant homomorphism preserves eigenvectors. -/
theorem map_mem_actionEigenvectors (χ : characterLattice S)
    {X : Additive (lieKernel G k)} (hX : X ∈ actionEigenvectors a χ) :
    Lie.targetMapLinear f k X ∈ actionEigenvectors b χ := by
  intro A _ _ s
  change b.act (Lie.constant S.toGrp s)
    (lieKernelMap K _ (Lie.targetMap f k X.toMul)).val = _
  simp only [lieKernelTargetLinear_toMul, ← lieKernelTarget_map,
    ← lieKernelTarget_scale, lieKernelTarget_val]
  rw [← hf, hX A s]

/-- Under a monomorphism, the image vector is an eigenvector exactly when the
source vector is an eigenvector. -/
theorem mem_actionEigenvectors_target_iff [Mono f.hom.hom]
    (χ : characterLattice S) (X : Additive (lieKernel G k)) :
    Lie.targetMapLinear f k X ∈ actionEigenvectors b χ ↔
      X ∈ actionEigenvectors a χ := by
  exact RelativeRoot.mem_actionEigenvectors_target_iff f inferInstance a b
    (fun _ s x => hf s x) χ X


/-- The actual derivative preserves every intrinsic action weight space. -/
theorem map_mem_actionWeightSpace (χ : characterLattice S)
    {X : Additive (lieKernel G k)} (hX : X ∈ actionWeightSpace a χ) :
    Lie.targetMapLinear f k X ∈ actionWeightSpace b χ := by
  exact RelativeRoot.lieKernelTargetLinear_mem_actionWeightSpace b a f
    (fun _ s x => hf s x) χ hX


/-- Restrict the actual derivative to the corresponding intrinsic weight spaces. -/
abbrev actionWeightSpaceMap (χ : characterLattice S) :
    actionWeightSpace a χ →ₗ[k] actionWeightSpace b χ :=
  RelativeRoot.actionWeightSpaceMap b a f (fun _ s x => hf s x) χ

@[simp] theorem actionWeightSpaceMap_apply_coe (χ : characterLattice S)
    (X : actionWeightSpace a χ) :
    (hf.actionWeightSpaceMap χ X : Additive (lieKernel K k)) =
      Lie.targetMapLinear f k X := rfl

/-- The restricted derivative is injective when the underlying homomorphism is. -/
theorem actionWeightSpaceMap_injective [Mono f.hom.hom] (χ : characterLattice S) :
    Function.Injective (hf.actionWeightSpaceMap χ) := by
  exact RelativeRoot.actionWeightSpaceMap_injective b a f
    (fun _ s x => hf s x) χ


/-- A monomorphic equivariant homomorphism reflects intrinsic action weights. -/
theorem mem_actionWeightSpace_target_iff [Mono f.hom.hom]
    (χ : characterLattice S) (X : Additive (lieKernel G k)) :
    Lie.targetMapLinear f k X ∈ actionWeightSpace b χ ↔
      X ∈ actionWeightSpace a χ := by
  exact RelativeRoot.mem_actionWeightSpace_target_iff f inferInstance a b
    (fun _ s x => hf s x) χ X


/-- Source weight spaces are the inverse images of target weight spaces. -/
theorem actionWeightSpace_eq_comap [Mono f.hom.hom] (χ : characterLattice S) :
    actionWeightSpace a χ =
      (actionWeightSpace b χ).comap (Lie.targetMapLinear f k) := by
  ext X
  exact (hf.mem_actionWeightSpace_target_iff χ X).symm

/-- The image weight space is the target weight space intersected with the
range of the actual derivative. -/
theorem map_actionWeightSpace_eq_inf_range [Mono f.hom.hom]
    (χ : characterLattice S) :
    (actionWeightSpace a χ).map (Lie.targetMapLinear f k) =
      actionWeightSpace b χ ⊓ LinearMap.range (Lie.targetMapLinear f k) := by
  simpa only [tangentSubmodule_range] using
    RelativeRoot.map_actionWeightSpace_eq_inf_tangentSubmodule b a f
      (fun _ s x => hf s x) χ


/-- Under an equivariant monomorphism, mapping an arbitrary subgroup functor
preserves its full intrinsic tangent-weight support. -/
theorem actionWeightSupport_map_eq [Mono f.hom.hom] (F : SubgroupFunctor G) :
    actionWeightSupport b (F.map f) = actionWeightSupport a F := by
  exact RelativeRoot.actionWeightSupport_map f inferInstance a b
    (fun _ s x => hf s x) F


end Langlands.GroupScheme.AutomorphicAction.IsEquivariant
