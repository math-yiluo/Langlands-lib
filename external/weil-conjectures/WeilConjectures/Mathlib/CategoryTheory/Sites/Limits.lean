/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Limits of sheaves and exactness of sheafification

Finite limits of presheaves are computed objectwise, the inclusion of sheaves into presheaves
preserves limits, and sheafification is exact.
-/

@[expose] public section

namespace CategoryTheory

open Limits

/-- **Finite limits of presheaves are objectwise.** For a category `A` with finite limits:
(1) every evaluation functor `G ↦ G(V)` on `A`-valued presheaves preserves finite limits, and a
functor into presheaves preserves finite limits as soon as all its composites with the
evaluations do; (2) the inclusion of sheaves into presheaves preserves finite limits; (3) when
sheafification exists, the counit of the sheafification adjunction is an isomorphism at every
sheaf. (blueprint: `situation-conventions`) -/
theorem presheaf_finiteLimits_objectwise {C : Type*} [Category* C] (J : GrothendieckTopology C)
    (A : Type*) [Category* A] [HasFiniteLimits A] :
    (∀ V : Cᵒᵖ, PreservesFiniteLimits ((evaluation Cᵒᵖ A).obj V)) ∧
      (∀ {D : Type*} [Category* D] (Φ : D ⥤ Cᵒᵖ ⥤ A),
        (∀ V, PreservesFiniteLimits (Φ ⋙ (evaluation Cᵒᵖ A).obj V)) → PreservesFiniteLimits Φ) ∧
      PreservesFiniteLimits (sheafToPresheaf J A) ∧
      ∀ [HasWeakSheafify J A] (F : Sheaf J A),
        IsIso ((sheafificationAdjunction J A).counit.app F) :=
  ⟨fun _ ↦ inferInstance, fun Φ h ↦ preservesFiniteLimits_of_evaluation Φ h, inferInstance,
    fun _ ↦ inferInstance⟩

/-- **Sheafification is exact.** The inclusion of sheaves into presheaves preserves all limits
(limits of sheaves are computed sectionwise, e.g. kernels), and sheafification preserves finite
limits and, being a left adjoint, all colimits. Applied to `A = Ab` this is the exactness of
sheafification of abelian presheaves. (blueprint: `situation-conventions`) -/
theorem sheafToPresheaf_preservesLimits_and_presheafToSheaf_exact {C : Type*} [Category* C]
    (J : GrothendieckTopology C) (A : Type*) [Category* A] [HasSheafify J A] [HasFiniteLimits A] :
    PreservesLimits (sheafToPresheaf J A) ∧ PreservesFiniteLimits (presheafToSheaf J A) ∧
      PreservesColimits (presheafToSheaf J A) :=
  ⟨inferInstance, inferInstance, (sheafificationAdjunction J A).leftAdjoint_preservesColimits⟩

end CategoryTheory
