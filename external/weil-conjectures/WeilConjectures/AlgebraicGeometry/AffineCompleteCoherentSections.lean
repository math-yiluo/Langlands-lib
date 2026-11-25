/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Category.ModuleCat.Limits

import WeilConjectures.AlgebraicGeometry.FormalFunctionsCompleteBase

/-! # Canonical inverse-limit sections over a complete affine base

Source: Stacks Project, Tag 087U, degree zero for the identity of Spec A.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual quotient projections identify sections of a coherent module over a
complete affine base with the inverse limit of its completed sections.
Source: Stacks Project, Tag 087U, degree zero for the identity of Spec A.
(blueprint: lem-weil-pbc-affine-complete-coherent-sections)

Proof: Apply degree-zero formal functions over the complete base to the proper
identity of Spec A. Comapping J along the identity gives J. The section functor
followed by restriction along the inverse of GammaSpecIso and the identity's
appTop is definitionally moduleSpecGammaFunctor. Rewrite the formal-functions
isomorphism and its projection equations along this functor equality. The actual
quotient maps are retained throughout. If I is the unit ideal, completeness
forces A and the section module to be zero, so the same assertion holds. -/
theorem affine_complete_coherent_sections
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    (J : (Spec (CommRingCat.of A)).IdealSheafData)
    (hJ : J = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
    (H : CoherentModules (Spec (CommRingCat.of A))) :
    ∃ e : (moduleSpecΓFunctor (R := CommRingCat.of A)).obj H.obj ≅
        limit (formalCompletionSystem J H.obj ⋙ moduleSpecΓFunctor (R := CommRingCat.of A)),
      ∀ n : ℕ, e.hom ≫ limit.π
          (formalCompletionSystem J H.obj ⋙ moduleSpecΓFunctor (R := CommRingCat.of A))
          (op n) =
        (moduleSpecΓFunctor (R := CommRingCat.of A)).map
          (formalModuleQuotientπ J (n + 1) H.obj) := by
  have hf := globalSections_formalFunctions_complete_base I
    (𝟙 (Spec (CommRingCat.of A))) H
  rw [Scheme.IdealSheafData.comap_id] at hf
  subst J
  have hc : RingedSpace.globalSectionsFunctor (Spec (CommRingCat.of A)).toRingedSpace ⋙
      ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
          Scheme.Hom.appTop (𝟙 (Spec (CommRingCat.of A)))).hom =
      moduleSpecΓFunctor (R := CommRingCat.of A) := by
    rfl
  rw [hc] at hf
  exact hf

end AlgebraicGeometry
