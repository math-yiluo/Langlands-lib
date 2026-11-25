/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import all WeilConjectures.AlgebraicGeometry.CoefficientComparisonFixedPullback
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-! # Geometric stalks on the coefficient-sized etale model

Source: Stacks Project, Tags 03PT and 04EQ.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Continuity of the original etale-site equivalence at the coefficient size.
Source: Stacks Tag 00VC (auxiliary; not a blueprint node). -/
instance coefficientEtaleAsSmallUp_isContinuous (X : Scheme.{u}) :
    (AsSmall.up : X.Etale ⥤ smallModelComparisonEtaleSite.{u, v} X).IsContinuous
      X.smallEtaleTopology (smallModelComparisonEtaleTopology.{u, v} X) :=
  inferInstanceAs
    ((AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).functor.IsContinuous
      X.smallEtaleTopology
      ((AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).inverse.inducedTopology
        X.smallEtaleTopology))

/-- The ordinary geometric stalk: restrict to constant scalars, undo AsSmall, and take
its usual pointed-neighborhood colimit. Source: Stacks Tags 03PT and 04EQ.
(auxiliary; not a blueprint node). -/
def coefficientEtaleModuleStalk (X : Scheme.{u})
    (B : Type (max v (u + 1))) [CommRing B]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    ConstantCompletion.Mod
      (ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, v} X) B) ⥤
      ModuleCat.{max v (u + 1)} B :=
  coefficientModelFixedScalars (smallModelComparisonEtaleTopology.{u, v} X) B ⋙
    (AsSmall.up : X.Etale ⥤ smallModelComparisonEtaleSite.{u, v} X).sheafPushforwardContinuous
      (ModuleCat.{max v (u + 1)} B)
        X.smallEtaleTopology (smallModelComparisonEtaleTopology.{u, v} X) ⋙
    (pointSmallEtale x).sheafFiber (A := ModuleCat.{max v (u + 1)} B)

/-- Geometric stalks on the model are additive and exact. Source: Stacks Tag 04EQ.
(auxiliary; not a blueprint node).

Proof: the two changes of presentation are equivalences. The remaining functor is
the usual exact geometric stalk, a filtered colimit of sections. -/
theorem coefficientEtaleModuleStalk_exact (X : Scheme.{u})
    (B : Type (max v (u + 1))) [CommRing B]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    (coefficientEtaleModuleStalk X B x).Additive ∧
      PreservesFiniteLimits (coefficientEtaleModuleStalk X B x) ∧
      PreservesFiniteColimits (coefficientEtaleModuleStalk X B x) := by
  have : HasLimitsOfSize.{u, u} (ModuleCat.{max v (u + 1)} B) :=
    ModuleCat.hasLimitsOfSize.{u, u, max v (u + 1), max v (u + 1)}
  have : HasColimitsOfSize.{u, u} (ModuleCat.{max v (u + 1)} B) :=
    inferInstance
  have : AB5OfSize.{u, u} (ModuleCat.{max v (u + 1)} B) :=
    AB5OfSize_of_univLE.{u, u, max v (u + 1), max v (u + 1)} _
  have : HasFiniteLimits
      (Sheaf X.smallEtaleTopology (ModuleCat.{max v (u + 1)} B)) := inferInstance
  have : HasBinaryBiproducts
      (Sheaf X.smallEtaleTopology (ModuleCat.{max v (u + 1)} B)) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  have : (AsSmall.down : smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).isEquivalence_inverse
  have : (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).inverse.IsDenseSubsite
      (smallModelComparisonEtaleTopology.{u, v} X) X.smallEtaleTopology := by
    change (AsSmall.down : smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale).IsDenseSubsite
      (AsSmall.down.inducedTopology X.smallEtaleTopology) X.smallEtaleTopology
    infer_instance
  have := ProEtale.scalars_equivalence (smallModelComparisonEtaleTopology.{u, v} X) B
  let F := coefficientModelFixedScalars (smallModelComparisonEtaleTopology.{u, v} X) B
  let G : Sheaf (smallModelComparisonEtaleTopology.{u, v} X)
      (ModuleCat.{max v (u + 1)} B) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{max v (u + 1)} B) :=
    (AsSmall.up : X.Etale ⥤ smallModelComparisonEtaleSite.{u, v} X).sheafPushforwardContinuous
      (ModuleCat.{max v (u + 1)} B)
      X.smallEtaleTopology (smallModelComparisonEtaleTopology.{u, v} X)
  have : F.Additive := ⟨by intro M N f g; ext V m; rfl⟩
  have : G.Additive := ⟨by intro M N f g; ext V m; rfl⟩
  have : G.IsEquivalence := by
    change ((AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).sheafCongr
      X.smallEtaleTopology (smallModelComparisonEtaleTopology.{u, v} X)
      (ModuleCat.{max v (u + 1)} B)).inverse.IsEquivalence
    infer_instance
  have : ((pointSmallEtale x).sheafFiber (A := ModuleCat.{max v (u + 1)} B)).Additive :=
    @GrothendieckTopology.Point.sheafFiber_additive.{u, max v (u + 1), max v (u + 1) + 1,
      u, u + 1} _ _ _ (pointSmallEtale x) (ModuleCat.{max v (u + 1)} B)
      (ModuleCat.moduleCategory.{max v (u + 1), max v (u + 1)} B)
      inferInstance inferInstance inferInstance inferInstance
  let H := (pointSmallEtale x).sheafFiber (A := ModuleCat.{max v (u + 1)} B)
  exact ⟨inferInstanceAs (F ⋙ G ⋙ H).Additive,
    inferInstanceAs (PreservesFiniteLimits (F ⋙ G ⋙ H)),
    inferInstanceAs (PreservesFiniteColimits (F ⋙ G ⋙ H))⟩

instance coefficientEtaleModuleStalk_additive (X : Scheme.{u})
    (B : Type (max v (u + 1))) [CommRing B]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    (coefficientEtaleModuleStalk X B x).Additive :=
  (coefficientEtaleModuleStalk_exact X B x).1

instance coefficientEtaleModuleStalk_limits (X : Scheme.{u})
    (B : Type (max v (u + 1))) [CommRing B]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    PreservesFiniteLimits (coefficientEtaleModuleStalk X B x) :=
  (coefficientEtaleModuleStalk_exact X B x).2.1

instance coefficientEtaleModuleStalk_colimits (X : Scheme.{u})
    (B : Type (max v (u + 1))) [CommRing B]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    PreservesFiniteColimits (coefficientEtaleModuleStalk X B x) :=
  (coefficientEtaleModuleStalk_exact X B x).2.2

/-- The exact derived geometric stalk of a constant-ring module complex, in the
independent coefficient universe. Source: Stacks Tags 03PT and 04EQ.
(auxiliary; not a blueprint node). -/
def coefficientEtaleDerivedStalk (X : Scheme.{u})
    (B : Type (max v (u + 1))) [CommRing B]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    ConstantCompletion.D
      (ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, v} X) B) ⥤
      DerivedCategory (ModuleCat.{max v (u + 1)} B) := by
  letI := HasDerivedCategory.standard (ConstantCompletion.Mod
    (ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, v} X) B))
  exact (coefficientEtaleModuleStalk X B x).mapDerivedCategory

end AlgebraicGeometry.Scheme
