import Langlands.GroupScheme.Lie.KernelTargetMaps
import Langlands.GroupScheme.Rational.TangentImage

/-! # Weight transport through actual equivariant subgroup representatives -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false



namespace RelativeRoot

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {H G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [IsAffineHom G.X.hom]
    (b : AutomorphicAction S.toGrp G) (d : AutomorphicAction S.toGrp H)
    (j : H ⟶ G)
    (hjd : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (x : T ⟶ H.X),
      d.act s x ≫ j.hom.hom = b.act s (x ≫ j.hom.hom))

include hjd

/-- An equivariant homomorphism preserves every intrinsic character weight space. -/
theorem lieKernelTargetLinear_mem_actionWeightSpace (χ : characterLattice S)
    {X : Additive (lieKernel H k)} (hX : X ∈ actionWeightSpace d χ) :
    Lie.targetMapLinear j k X ∈ actionWeightSpace b χ := by
  rw [mem_actionWeightSpace_iff] at hX ⊢
  intro A _ _ s
  have h := congrArg (fun x => x ≫ j.hom.hom) (hX A s)
  rw [hjd] at h
  simpa only [lieKernelMap_val, lieKernelScale_val, Lie.affineMap_apply,
    lieKernelTargetLinear_val, Category.assoc] using h

/-- The induced linear map between the source and ambient intrinsic weight spaces. -/
def actionWeightSpaceMap (χ : characterLattice S) :
    actionWeightSpace d χ →ₗ[k] actionWeightSpace b χ where
  toFun X := ⟨Lie.targetMapLinear j k X,
    lieKernelTargetLinear_mem_actionWeightSpace b d j hjd χ X.property⟩
  map_add' X Y := Subtype.ext (map_add (Lie.targetMapLinear j k)
    (X : Additive (lieKernel H k)) (Y : Additive (lieKernel H k)))
  map_smul' c X := Subtype.ext (map_smul (Lie.targetMapLinear j k) c
    (X : Additive (lieKernel H k)))

@[simp] theorem actionWeightSpaceMap_coe (χ : characterLattice S)
    (X : actionWeightSpace d χ) :
    (actionWeightSpaceMap b d j hjd χ X : Additive (lieKernel G k)) =
      Lie.targetMapLinear j k X := rfl

variable [Mono j.hom.hom]

/-- A monomorphic equivariant homomorphism also reflects intrinsic character weights. -/
theorem lieKernelTargetLinear_mem_actionWeightSpace_iff (χ : characterLattice S)
    (X : Additive (lieKernel H k)) :
    Lie.targetMapLinear j k X ∈ actionWeightSpace b χ ↔ X ∈ actionWeightSpace d χ := by
  constructor
  · intro hX
    rw [mem_actionWeightSpace_iff] at hX ⊢
    intro A _ _ s
    apply (cancel_mono j.hom.hom).mp
    rw [hjd]
    simpa only [lieKernelMap_val, lieKernelScale_val, Lie.affineMap_apply,
      lieKernelTargetLinear_val, Category.assoc] using hX A s
  · exact lieKernelTargetLinear_mem_actionWeightSpace b d j hjd χ

/-- The induced map on each weight space is injective for a monomorphic homomorphism. -/
theorem actionWeightSpaceMap_injective (χ : characterLattice S) :
    Function.Injective (actionWeightSpaceMap b d j hjd χ) := by
  intro X Y h
  apply Subtype.ext
  apply Lie.targetMapLinear_injective j k
  exact congrArg (fun Z : actionWeightSpace b χ => (Z : Additive (lieKernel G k))) h

/-- The image of the source weight space is precisely the intersection of the
ambient weight space with the actual tangent image of the subgroup. -/
theorem map_actionWeightSpace_eq_inf_tangentSubmodule (χ : characterLattice S) :
    (actionWeightSpace d χ).map (Lie.targetMapLinear j k) =
      actionWeightSpace b χ ⊓ tangentSubmodule (SubgroupFunctor.range j) := by
  ext X
  constructor
  · rintro ⟨Y, hY, rfl⟩
    exact ⟨lieKernelTargetLinear_mem_actionWeightSpace b d j hjd χ hY,
      ⟨Y.toMul.val, rfl⟩⟩
  · rintro ⟨hX, hF⟩
    rw [tangentSubmodule_range j] at hF
    obtain ⟨Y, rfl⟩ := hF
    exact ⟨Y, (lieKernelTargetLinear_mem_actionWeightSpace_iff b d j hjd χ Y).mp hX, rfl⟩

/-- Ambient support of a monomorphic equivariant subgroup records exactly
the nonzero intrinsic source weight spaces. -/
theorem mem_actionWeightSupport_range_iff (χ : characterLattice S) :
    χ ∈ actionWeightSupport b (SubgroupFunctor.range j) ↔ actionWeightSpace d χ ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  constructor
  · rintro ⟨X, hX0, hX, hF⟩
    have hF' : X ∈ tangentSubmodule (SubgroupFunctor.range j) := hF
    rw [tangentSubmodule_range j] at hF'
    obtain ⟨Y, rfl⟩ := hF'
    refine ⟨Y, (lieKernelTargetLinear_mem_actionWeightSpace_iff b d j hjd χ Y).mp hX, ?_⟩
    intro hY
    exact hX0 (by rw [hY, map_zero])
  · rintro ⟨Y, hY, hY0⟩
    refine ⟨Lie.targetMapLinear j k Y, ?_,
      lieKernelTargetLinear_mem_actionWeightSpace b d j hjd χ hY, ⟨Y.toMul.val, rfl⟩⟩
    intro h
    apply hY0
    apply Lie.targetMapLinear_injective j k
    simpa only [map_zero] using h

omit hjd

section RepresentedAction

variable {F : SubgroupFunctor G} (hj : F.IsRepresentedBy j) (hF : b.IsStable F)

omit [Mono j.hom.hom] in
/-- The ambient support of a represented stable subgroup is the set of its
nonzero intrinsic weight spaces for the actual induced action. -/
theorem mem_actionWeightSupport_iff_onRepresentedSubgroup (χ : characterLattice S) :
    χ ∈ actionWeightSupport b F ↔
      actionWeightSpace (b.onRepresentedSubgroup j hj hF) χ ≠ ⊥ := by
  have : Mono j.hom.hom := hj.1
  have h := mem_actionWeightSupport_range_iff b (b.onRepresentedSubgroup j hj hF) j
    (fun _ s x => b.onRepresentedSubgroup_act_comp j hj hF s x) χ
  simpa only [hj.2] using h

omit [Mono j.hom.hom] in
/-- Excluding a character from ambient support makes its intrinsic source
weight space zero for the induced action. In particular this applies to zero. -/
theorem actionWeightSpace_onRepresentedSubgroup_eq_bot
    (χ : characterLattice S) (hχ : χ ∉ actionWeightSupport b F) :
    actionWeightSpace (b.onRepresentedSubgroup j hj hF) χ = ⊥ := by
  by_contra h
  exact hχ ((mem_actionWeightSupport_iff_onRepresentedSubgroup b j hj hF χ).mpr h)

end RepresentedAction
end RelativeRoot
end Langlands.GroupScheme
