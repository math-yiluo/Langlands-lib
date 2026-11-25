/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf

/-! # Exactness of constant module sheafification

Source: Stacks Project, Modules on Sites, Tag 093U (3), kernel and cokernel argument.
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- The constant module sheaf functor preserves finite limits and finite colimits.
Source: Stacks Project, Modules on Sites, Tag 093U (3).
(auxiliary; not a blueprint node).

Proof: Evaluation of the constant module presheaf functor at any object is the identity
functor on modules. Limits and colimits of presheaves of modules are sectionwise, so this
functor preserves both. Module sheafification preserves finite limits and, as a left
adjoint, all colimits. Compose these preservation properties. In particular, applying
the kernel and cokernel comparisons identifies the kernel and cokernel of a constant
linear map with the constants of its algebraic kernel and cokernel. -/
theorem strictPerfectConstantSheaf_exact {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (B : Type u) [CommRing B] :
    PreservesFiniteLimits (strictPerfectConstantSheaf J B) ∧
      PreservesFiniteColimits (strictPerfectConstantSheaf J B) := by
  constructor
  · let P := SheafOfModules.strictPerfectConstantPresheaf (C := C) B
    have : PreservesFiniteLimits P := by
      constructor
      intro K _ _
      constructor
      intro D
      apply preservesLimit_of_preserves_limit_cone (limit.isLimit D)
      apply PresheafOfModules.evaluationJointlyReflectsLimits
      intro X
      change IsLimit ((P ⋙ PresheafOfModules.evaluation _ X).mapCone (limit.cone D))
      have he : P ⋙ PresheafOfModules.evaluation _ X ≅ 𝟭 (ModuleCat.{u} B) := Iso.refl _
      let : PreservesLimitsOfShape K (P ⋙ PresheafOfModules.evaluation _ X) :=
        preservesLimitsOfShape_of_natIso he.symm
      exact isLimitOfPreserves _ (limit.isLimit D)
    exact comp_preservesFiniteLimits P _
  · let P := SheafOfModules.strictPerfectConstantPresheaf (C := C) B
    have : PreservesFiniteColimits P := by
      constructor
      intro K _ _
      constructor
      intro D
      apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit D)
      apply PresheafOfModules.evaluationJointlyReflectsColimits
      intro X
      change IsColimit ((P ⋙ PresheafOfModules.evaluation _ X).mapCocone (colimit.cocone D))
      have he : P ⋙ PresheafOfModules.evaluation _ X ≅ 𝟭 (ModuleCat.{u} B) := Iso.refl _
      let : PreservesColimitsOfShape K (P ⋙ PresheafOfModules.evaluation _ X) :=
        preservesColimitsOfShape_of_natIso he.symm
      exact isColimitOfPreserves _ (colimit.isColimit D)
    exact comp_preservesFiniteColimits P _

end SheafOfModules
