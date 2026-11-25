/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeTensorUnit
import WeilConjectures.AlgebraicGeometry.PicardPullbackBaseChangePrimal
import WeilConjectures.AlgebraicGeometry.PicardPullbackBaseChangeDual

/-! # Canonical base change for a pulled-back module

Source: Stacks Project, Tags 0BDP and 01E8.
(blueprint: lem-sc-picard-pullback-base-change)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Both canonical direct-image base-change maps are invertible for a module
pulled back from the base and its dual.
Source: Stacks Project, Tag 0BDP, projection-formula paragraph, using Tag 01E8;
Tag 08HY for the adjoint-defined canonical map.
(blueprint: lem-sc-picard-pullback-base-change)

Proof: Put p = X_T → T, v = X_T ×_T T' → X_T and p' = X_T ×_T T' → T'.
Pullback composition transports v^*p^*N to p'^*h^*N. The iterated fibre product
is canonically X_{T'}, so the structure-module unit hypothesis at h ≫ g
applies to p' after this identification. The finite-locally-free unit theorem
therefore identifies p_*p^*N with N and p'_*p'^*h^*N with h^*N. Under these
identifications the canonical map is identity on h^*N: insert m ↦ 1 ⊗ m in
the adjoint definition of moduleBaseChangeMap, compose the two pushforward
identifications, and use tensor associativity to identify 1 ⊗ (1 ⊗ m) with
1 ⊗ m. This calculation can be made on finite local frames of N; their
pullbacks cover T', and equality and invertibility glue. Naturality of the
base-change map transports invertibility through e. Pullback commutes with
duals of finite locally free modules, as the coordinate dual frame calculation
shows, so the identical argument applies to E^dual and N^dual. Rank zero
uses zero maps between zero modules, which are isomorphisms; empty bases
require no local checks. -/
theorem picard_pullback_base_change {X S T : Scheme.{u}}
    (f : X ⟶ S)
    (hO : ∀ {T' : Scheme.{u}} (g' : T' ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd f g'))).unit.app
          (SheafOfModules.unit T'.ringCatSheaf)))
    (E : X.Modules) [E.IsFiniteLocallyFree] (g : T ⟶ S) (N : T.Modules) [N.IsFiniteLocallyFree]
    (e : Nonempty ((Modules.tensorPullback (pullback.fst f g)).obj E ≅
      (Modules.tensorPullback (pullback.snd f g)).obj N)) :
    ∀ {T' : Scheme.{u}} (h : T' ⟶ T),
      IsIso (Modules.moduleBaseChangeMap (pullback.snd f g)
        (pullback.snd (pullback.snd f g) h) h (pullback.fst (pullback.snd f g) h)
        pullback.condition ((Modules.tensorPullback (pullback.fst f g)).obj E)) ∧
      IsIso (Modules.moduleBaseChangeMap (pullback.snd f g)
        (pullback.snd (pullback.snd f g) h) h (pullback.fst (pullback.snd f g) h)
        pullback.condition
          ((Modules.tensorPullback (pullback.fst f g)).obj (Modules.dual E))) := by
  intro T' h
  exact ⟨picard_pullback_base_change_primal f hO E g N e h,
    picard_pullback_base_change_dual f hO E g N e h⟩

end AlgebraicGeometry.Scheme
