import Langlands.GroupScheme.Lie.Functoriality
import Langlands.GroupScheme.Rational.StandardLeviTorusFactor
import Langlands.GroupScheme.Rational.GenericLieWeights
import Langlands.GroupScheme.Dynamic.LieStatement

/-! # Selected-root weight spaces in actual standard Levi representatives -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G L : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom L.X.hom]

/-- The differential of a represented subgroup has exactly the tangent vectors
whose actual dual-number points belong to that subgroup functor. -/
theorem SubgroupFunctor.IsRepresentedBy.mem_range_lieKernelHomLinear
    {F : SubgroupFunctor G} {j : L ⟶ G} (hj : F.IsRepresentedBy j)
    (X : Additive (lieKernel G k)) :
    X ∈ LinearMap.range (Lie.targetMapLinear j _) ↔
      X.toMul.val ∈ F.carrier _ := by
  have : Mono j.hom.hom := hj.1
  constructor
  · rintro ⟨Y, rfl⟩
    exact (hj.pointsEquiv _ Y.toMul.val).property
  · intro hX
    let Y := (hj.pointsEquiv _).symm ⟨X.toMul.val, hX⟩
    have hcomp : Y ≫ j.hom.hom = X.toMul.val :=
      hj.pointsEquiv_symm_comp _
    have hY : Lie.reduction L Y = 1 := by
      apply (cancel_mono j.hom.hom).mp
      change Lie.reduction G (Y ≫ j.hom.hom) = 1 ≫ j.hom.hom
      rw [hcomp, X.toMul.property, MonObj.one_comp]
    refine ⟨Additive.ofMul ⟨Y, hY⟩, ?_⟩
    apply Additive.toMul.injective
    exact Subtype.ext hcomp

variable [LocallyOfFiniteType G.X.hom]
  (hDynamic : DynamicLieStatement.{u})
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (J : Set (characterLattice T)) {j : L ⟶ G}
  (hj : (standardLevi i ν J).IsRepresentedBy j)

include hDynamic hj

/-- Selected-root vectors belong to the actual tangent image of the standard Levi.
This uses the centralizer clause of `DynamicLieStatement`. -/
theorem weightSpace_le_range_standardLeviTorusFactor
    {α : characterLattice T} (hα : α ∈ J) :
    weightSpace i α ≤ LinearMap.range (Lie.targetMapLinear j _) := by
  intro X hX
  apply (hj.mem_range_lieKernelHomLinear X).mpr
  rw [mem_standardLevi]
  intro zeta hzeta
  apply (hDynamic k G (CommGroupScheme.groupHom zeta ≫ i) X.toMul).1.mpr
  have hcomp : zeta ≫ α = Gm.powerHom _ 0 := by
    apply (gmEndEquiv k).injective
    simpa only [latticePairing_apply, Gm.powerHom, zero_smul, map_zero]
      using hzeta.2.1 α hα
  have h := weightSpace_le_comp zeta i α hX
  rwa [hcomp] at h

/-- The differential identifies each selected-root weight space in the actual
Levi representative with its ambient weight space. -/
theorem map_weightSpace_standardLeviTorusFactor
    {α : characterLattice T} (hα : α ∈ J) :
    (weightSpace (standardLeviTorusFactor i ν J hj) α).map
      (Lie.targetMapLinear j _) = weightSpace i α := by
  have : Mono j.hom.hom := hj.1
  apply le_antisymm
  · rintro X ⟨Y, hY, rfl⟩
    have h := lieKernelHomLinear_mem_weightSpace j
      (standardLeviTorusFactor i ν J hj) α hY
    rwa [standardLeviTorusFactor_comp] at h
  · intro X hX
    obtain ⟨Y, hY⟩ :=
      weightSpace_le_range_standardLeviTorusFactor hDynamic i ν J hj hα hX
    refine ⟨Y, ?_, hY⟩
    apply (lieKernelHomLinear_mem_weightSpace_iff j
      (standardLeviTorusFactor i ν J hj) α Y).mp
    rw [standardLeviTorusFactor_comp, hY]
    exact hX

/-- The actual differential gives a linear equivalence on each selected-root
weight space, conditional on the published dynamic Lie proposition. -/
def standardLeviWeightSpaceEquiv
    {α : characterLattice T} (hα : α ∈ J) :
    weightSpace (standardLeviTorusFactor i ν J hj) α ≃ₗ[k] weightSpace i α := by
  have : Mono j.hom.hom := hj.1
  exact (Submodule.equivMapOfInjective (Lie.targetMapLinear j _)
    (Lie.targetMapLinear_injective j _)
    (weightSpace (standardLeviTorusFactor i ν J hj) α)).trans
      (LinearEquiv.ofEq _ _
        (map_weightSpace_standardLeviTorusFactor hDynamic i ν J hj hα))

@[simp] theorem standardLeviWeightSpaceEquiv_coe
    {α : characterLattice T} (hα : α ∈ J)
    (X : weightSpace (standardLeviTorusFactor i ν J hj) α) :
    (standardLeviWeightSpaceEquiv hDynamic i ν J hj hα X :
      Additive (lieKernel G k)) = Lie.targetMapLinear j _ X := rfl

/-- Every selected simple root is a root of the actual standard Levi representative.
No reductivity or root-system conclusion is assumed for that representative. -/
theorem selectedRoots_subset_relativeRoots_standardLeviTorusFactor
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    J ⊆ relativeRoots (standardLeviTorusFactor i ν J hj) := by
  intro α hα
  have hroot : α ∈ relativeRoots i :=
    positiveRelativeRoots_subset_relativeRoots i ν
      (simpleRelativeRoots_subset_positive i ν (hJ hα))
  refine ⟨hroot.1, ?_⟩
  intro hbot
  have hmap := map_weightSpace_standardLeviTorusFactor hDynamic i ν J hj hα
  rw [hbot, Submodule.map_bot] at hmap
  exact hroot.2 hmap.symm

end Langlands.GroupScheme
