/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicImmersionCompletedModel
public import WeilConjectures.AlgebraicGeometry.AdicImmersionResidueTransport

/-! # Fixed residue pullback data

Source: Stacks Tags 03A0 and 03CY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

attribute [local instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

namespace SfbResidueComparisonCore

private local instance modelSheafify (S : Scheme.{u}) :
    HasSheafify (proEtaleModelTopology S) AddCommGrpCat.{u + 1} :=
  SheafOfModules.hasSheafify_coefficientUniverse.{u + 1, u + 1, u + 1}

private local instance modelLocallyBijective (S : Scheme.{u}) :
    (proEtaleModelTopology S).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u + 1, u + 1, u + 1}

private local instance fixedSheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  SheafOfModules.hasSheafify_coefficientUniverse.{u + 1, u, u + 1}

attribute [local instance 50000] modelSheafify modelLocallyBijective fixedSheafify

private local instance standardDerived {D : Type (u + 1)} [SmallCategory D]
    {J : GrothendieckTopology D} (O : Sheaf J CommRingCat.{u + 1}) :
    HasDerivedCategory (ConstantCompletion.Mod O) := HasDerivedCategory.standard _

private local instance fixedLocallyBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u + 1, u, u + 1}

private noncomputable local instance modelAbelian (S : Scheme.{u})
    (R : Sheaf (proEtaleModelTopology S) CommRingCat.{u + 1}) :
    Abelian (ConstantCompletion.Mod R) :=
  SheafOfModules.instAbelian.{u + 1, u + 1, u + 1, u + 1} _

private noncomputable local instance fixedAbelian (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    Abelian (proEtaleRingModules X R) :=
  SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1} _

attribute [local instance 40000] modelAbelian fixedAbelian standardDerived
  fixedLocallyBijective
attribute [local instance 30000] proEtaleRingModules_hasDerivedCategory

/-- Pure inverse image of a fixed-scalar residue, followed by the actual small-site
and constant-ring equivalences. No completed coefficient ring occurs in this functor.
Source: Stacks Tags 03A0 and 03CY
(auxiliary; not a blueprint node). -/
def sfbFixedResiduePull {X S : Scheme.{u}} (i : S ⟶ X)
    (k : Type (u + 1)) [CommRing k] :
    Sheaf (ProEt.topology X) (ModuleCat.{u + 1} k) ⥤
      ConstantCompletion.Mod (ConstantCompletion.constant (proEtaleModelTopology S) k) :=
  proEtaleSheafInverseImage i (ModuleCat.{u + 1} k) ⋙
    (SfbAdicRestriction.modelEquivalence S (ModuleCat.{u + 1} k)).inverse ⋙
      (ConstantScalarRestriction.restriction (proEtaleModelTopology S) k).asEquivalence.inverse

instance sfbFixedResiduePull_limits {X S : Scheme.{u}} (i : S ⟶ X)
    (k : Type (u + 1)) [CommRing k] : PreservesFiniteLimits (sfbFixedResiduePull i k) := by
  have : (SfbAdicRestriction.modelEquivalence S (ModuleCat.{u + 1} k)).inverse.IsEquivalence :=
    (SfbAdicRestriction.modelEquivalence S (ModuleCat.{u + 1} k)).isEquivalence_inverse
  have : (ConstantScalarRestriction.restriction (proEtaleModelTopology S)
      k).asEquivalence.inverse.IsEquivalence :=
    CategoryTheory.Equivalence.isEquivalence_inverse
      (ConstantScalarRestriction.restriction (proEtaleModelTopology S) k).asEquivalence
  have : RepresentablyFlat (proEtaleBaseChange i) :=
    flat_of_preservesFiniteLimits (proEtaleBaseChange i)
  have : PreservesFiniteLimits (proEtaleSheafInverseImage i (ModuleCat.{u + 1} k)) :=
    Functor.sheafPullbackConstruction.instPreservesFiniteLimitsSheafSheafPullback
      (proEtaleBaseChange i) (ModuleCat.{u + 1} k) (ProEt.topology X) (ProEt.topology S)
  unfold sfbFixedResiduePull
  infer_instance

instance sfbFixedResiduePull_colimits {X S : Scheme.{u}} (i : S ⟶ X)
    (k : Type (u + 1)) [CommRing k] : PreservesFiniteColimits (sfbFixedResiduePull i k) := by
  have : (SfbAdicRestriction.modelEquivalence S (ModuleCat.{u + 1} k)).inverse.IsEquivalence :=
    (SfbAdicRestriction.modelEquivalence S (ModuleCat.{u + 1} k)).isEquivalence_inverse
  have : (ConstantScalarRestriction.restriction (proEtaleModelTopology S)
      k).asEquivalence.inverse.IsEquivalence :=
    CategoryTheory.Equivalence.isEquivalence_inverse
      (ConstantScalarRestriction.restriction (proEtaleModelTopology S) k).asEquivalence
  have : (proEtaleSheafInverseImage i (ModuleCat.{u + 1} k)).IsLeftAdjoint :=
    (proEtaleSheafAdjunction i (ModuleCat.{u + 1} k)).isLeftAdjoint
  unfold sfbFixedResiduePull
  infer_instance

instance sfbFixedResiduePull_additive {X S : Scheme.{u}} (i : S ⟶ X)
    (k : Type (u + 1)) [CommRing k] : (sfbFixedResiduePull i k).Additive := by
  exact Functor.additive_of_preserves_binary_products _

end SfbResidueComparisonCore

end AlgebraicGeometry.Scheme
