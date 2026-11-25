/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedModuleBaseChangeMap

/-! # Existence of the derived-to-ordinary module pullback comparison

Source: Stacks Project, Cohomology, Remark 08HY.
(blueprint: lem-pc-canonical-module-base-change-open-comparison-c0,
stage3-canonicalModuleBaseChange_iso_comparison_c0).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- For every morphism of schemes `a : X ⟶ Y` and every module `G` on `Y`, there is a map
`La^*(G[0]) ⟶ (a^*G)[0]` which is the derived-to-ordinary pullback comparison at `G`.
Source: Stacks Project, Cohomology, Remark 08HY.

Proof: the specification of the chosen derived pullback supplies an additive underived functor,
equal to `tensorPullback a` on objects and maps, together with a left-derived counit `ε`.
Evaluate `ε` at `G[0]` in the homotopy category and compose with the localization of the
identification of `a^*` applied to `G[0]` with `(a^*G)[0]`. -/
theorem exists_isDerivedModulePullbackComparison
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (a : X ⟶ Y) [(Scheme.Modules.tensorPullback a).Additive]
    (G : Y.Modules) :
    ∃ c : (derivedPullback a).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj G) ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback a).obj G),
      IsDerivedModulePullbackComparison a G c := by
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    E, hE, hEmap, hEadd, ε, hε, htri, hK⟩ :=
    derivedPullback_spec a
  have h : E = Scheme.Modules.tensorPullback a :=
    CategoryTheory.Functor.ext hE (fun _ _ φ ↦ hEmap φ)
  subst E
  exact ⟨_, ε, hε, rfl⟩

end AlgebraicGeometry
