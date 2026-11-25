/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

/-! # Canonical base change for a module in degree zero

Source: Stacks Project, Cohomology, Remark 08HY and Derived Categories of Schemes,
Tag 0B91 (blueprint: def-pc-derived-module-base-change-map).

## Main definitions

* `IsDerivedModulePullbackComparison`: a map is the derived-to-ordinary pullback
  comparison at a module.
* `IsDerivedModuleBaseChangeMap`: a map is the base change with the ordinary pulled-back
  module as target.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe uMB wMB
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- `c` is the canonical comparison `La^*(G[0]) ⟶ (a^*G)[0]` from derived to ordinary
pullback of a module: the left-derived counit of `La^*` at `G[0]`, for a left-derived
structure of `La^*` over the termwise tensor pullback, followed by the identification of
`a^*` applied to `G[0]` with `(a^*G)[0]`. Transposed under `La^* ⊣ Ra_*`, pinned to the
same counit, this is the ordinary pullback unit in degree zero followed by
`a_* ⟶ Ra_*`. Source: Stacks, Cohomology, Remark 08HY
(blueprint: def-pc-derived-module-base-change-map). -/
def IsDerivedModulePullbackComparison
    [∀ Y : Scheme.{uMB},
      HasDerivedCategory.{wMB} (SheafOfModules.{uMB} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{uMB}} (a : X ⟶ Y) [(Scheme.Modules.tensorPullback a).Additive]
    (G : Y.Modules)
    (c : (derivedPullback a).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{uMB} (moduleRings Y.toRingedSpace)) 0).obj G) ⟶
      (DerivedCategory.singleFunctor
          (SheafOfModules.{uMB} (moduleRings X.toRingedSpace)) 0).obj
        ((Scheme.Modules.tensorPullback a).obj G)) : Prop :=
  ∃ ε : DerivedCategory.Qh ⋙ derivedPullback a ⟶
      (Scheme.Modules.tensorPullback a).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh (C := SheafOfModules.{uMB} (moduleRings X.toRingedSpace)),
    (derivedPullback a).IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso
          (SheafOfModules.{uMB} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)) ∧
      c = cast (by rfl) (ε.app ((HomotopyCategory.singleFunctor
            (SheafOfModules.{uMB} (moduleRings Y.toRingedSpace)) 0).obj G) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex
            (Scheme.Modules.tensorPullback a) (ComplexShape.up ℤ) 0).hom.app G)))

/-- `φ` is the canonical module base-change map `Lg^*Rf_*(G[0]) ⟶ Rf_{T,*}((g_X^*G)[0])`:
the derived base-change map of the chosen fibre square followed by the derived direct
image of the derived-to-ordinary pullback comparison at `G`.
Source: Stacks Project, Tag 0B91, clause (2), and Cohomology, Remark 08HY
(blueprint: def-pc-derived-module-base-change-map). -/
def IsDerivedModuleBaseChangeMap
    [∀ Y : Scheme.{uMB},
      HasDerivedCategory.{wMB} (SheafOfModules.{uMB} (moduleRings Y.toRingedSpace))]
    {X S T : Scheme.{uMB}} (f : X ⟶ S) (g : T ⟶ S)
    [(Scheme.Modules.tensorPullback (pullback.fst f g)).Additive] (G : X.Modules)
    (φ : (derivedPullback g).obj
        ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{uMB} (moduleRings X.toRingedSpace)) 0).obj G)) ⟶
      (schemeDerivedDirectImage (pullback.snd f g)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{uMB} (moduleRings (pullback f g).toRingedSpace)) 0).obj
          ((Scheme.Modules.tensorPullback (pullback.fst f g)).obj G))) : Prop :=
  ∃ c, IsDerivedModulePullbackComparison (pullback.fst f g) G c ∧
    φ = schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition ((DerivedCategory.singleFunctor
          (SheafOfModules.{uMB} (moduleRings X.toRingedSpace)) 0).obj G) ≫
      (schemeDerivedDirectImage (pullback.snd f g)).map c

end AlgebraicGeometry
