/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
import Mathlib.CategoryTheory.Sites.Adjunction
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering

/-! # Universal arrows for derived coefficient normalization

Source: Stacks Project, Tags 06YY, 07A6 and 06Y5, derived extension and its adjunction
(auxiliary; not a blueprint node).

A normalization isomorphism can equivalently be supplied by its universal arrow to
restriction of scalars. This encoding retains its specific arrow, and avoids choosing
an additional model of the total derived tensor functor.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R S : Type (u + 1)} [CommRing R] [CommRing S]

/-- Constant module sheaves are exact, and restriction of coefficient scalars on module
sheaves is additive and exact. These are the exact functors used below.
Source: Stacks Tags 093J, 03DA and 06YY
(auxiliary; not a blueprint node).
Proof: constant presheaves preserve all finite limits and colimits. Sheafification is
left exact and is a left adjoint, so the constant sheaf functor is exact. Restriction of
scalars preserves all module limits and colimits; limits of sheaves are sectionwise, and
colimits are sheafifications of presheaf colimits. Since restriction of scalars preserves
sheafification, it preserves these colimits too. It is additive on sections. -/
theorem normalizationCoefficientExactness (q : R →+* S) :
    (PreservesFiniteLimits (constantSheaf J (ModuleCat.{u + 1} R)) ∧
      PreservesFiniteColimits (constantSheaf J (ModuleCat.{u + 1} R))) ∧
    ((sheafCompose J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).Additive ∧
      PreservesFiniteLimits (sheafCompose J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)) ∧
      PreservesFiniteColimits (sheafCompose J
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q))) ∧
    J.PreservesSheafification (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) := by
  have : (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} q).isLeftAdjoint
  have : (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q).IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} q).isRightAdjoint
  have : (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} q).IsRightAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} q).isRightAdjoint
  have : (sheafCompose J
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).IsLeftAdjoint :=
    (sheafComposeAdjunction J
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} q)).isLeftAdjoint
  exact ⟨⟨inferInstance, inferInstance⟩,
    ⟨inferInstance, inferInstance, inferInstance⟩, inferInstance⟩

/-- Exactness of constants, from the coefficient exactness statement.
Source: Stacks Tag 093J (auxiliary; not a blueprint node). -/
noncomputable instance normalizationConstantLimits :
    PreservesFiniteLimits (constantSheaf J (ModuleCat.{u + 1} R)) :=
  (normalizationCoefficientExactness J (RingHom.id R)).1.1

/-- Exactness of constants, from the coefficient exactness statement.
Source: Stacks Tag 093J (auxiliary; not a blueprint node). -/
noncomputable instance normalizationConstantColimits :
    PreservesFiniteColimits (constantSheaf J (ModuleCat.{u + 1} R)) :=
  (normalizationCoefficientExactness J (RingHom.id R)).1.2

/-- Additivity of coefficient restriction.
Source: Stacks Tag 03DA (auxiliary; not a blueprint node). -/
noncomputable instance normalizationRestrictAdditive (q : R →+* S) :
    (sheafCompose J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).Additive :=
  (normalizationCoefficientExactness J q).2.1.1

/-- Left exactness of coefficient restriction.
Source: Stacks Tag 03DA (auxiliary; not a blueprint node). -/
noncomputable instance normalizationRestrictLimits (q : R →+* S) :
    PreservesFiniteLimits (sheafCompose J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)) :=
  (normalizationCoefficientExactness J q).2.1.2.1

/-- Right exactness of coefficient restriction.
Source: Stacks Tag 03DA (auxiliary; not a blueprint node). -/
noncomputable instance normalizationRestrictColimits (q : R →+* S) :
    PreservesFiniteColimits (sheafCompose J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)) :=
  (normalizationCoefficientExactness J q).2.1.2.2

/-- Coefficient restriction commutes with sheafification.
Source: Stacks Tag 03DA (auxiliary; not a blueprint node). -/
noncomputable instance normalizationRestrictSheafification (q : R →+* S) :
    J.PreservesSheafification (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) :=
  (normalizationCoefficientExactness J q).2.2

section Pullback

variable {D : Type (u + 1)} [Category.{u} D] [EssentiallySmall.{u + 1} D]
  (F : C ⥤ D) (K : GrothendieckTopology D) [F.IsContinuous J K]

end Pullback

end CategoryTheory
