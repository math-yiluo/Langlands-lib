/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

import WeilConjectures.AlgebraicGeometry.PicardPullbackBaseChangePrimal
import WeilConjectures.AlgebraicGeometry.PullbackDualFiniteLocallyFree

/-! # Base change for the dual of a pulled-back finite locally free module

Source: Stacks Project, Tag 0BDP, projection-formula paragraph, and Tag 0FNV.
(blueprint: lem-sc-picard-pullback-base-change-dual)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
/-- Uniqueness of left adjoints transports the ordinary pullback-duality comparison
of Tag 0FNV to the explicit tensor-formula pullback. -/
private theorem tensorPullback_dual_iso {A B : Scheme.{u}} (k : A ⟶ B)
    (M : B.Modules) [M.IsFiniteLocallyFree] :
    Nonempty ((Modules.tensorPullback k).obj (Modules.dual M) ≅
      Modules.dual ((Modules.tensorPullback k).obj M)) := by
  let c := (Classical.choose (Modules.exists_tensorPullbackAdjunction k)).leftAdjointUniq
    (Modules.pullbackPushforwardAdjunction k)
  obtain ⟨d⟩ := Modules.nonempty_pullback_dual_iso_of_isFiniteLocallyFree k M
  exact ⟨c.app (Modules.dual M) ≪≫ d ≪≫ (Modules.dualFunctor A).mapIso (c.app M).op⟩

/-- The dual base-change map for a pulled-back finite locally free module is invertible.
Source: Stacks Project, Tag 0BDP, projection-formula paragraph, after dualizing frames.
(blueprint: lem-sc-picard-pullback-base-change-dual)
Proof: Duals of finite locally free modules are finite locally free. Uniqueness of
left adjoints identifies tensor pullback with ordinary module pullback, so the
pullback-duality comparison gives P_k(M^dual) ≅ (P_k M)^dual. Apply this comparison
at both projections and apply the contravariant dual functor to e, obtaining
P_q(E^dual) ≅ P_p(N^dual). The primal base-change theorem with E^dual and N^dual
now gives the claimed isomorphism for every h. This includes rank zero, empty
schemes and arbitrary ranks varying locally; no extra hypotheses are needed. -/
theorem picard_pullback_base_change_dual {X S T : Scheme.{u}}
    (f : X ⟶ S)
    (hO : ∀ {T' : Scheme.{u}} (g' : T' ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd f g'))).unit.app
          (SheafOfModules.unit T'.ringCatSheaf)))
    (E : X.Modules) [E.IsFiniteLocallyFree] (g : T ⟶ S) (N : T.Modules) [N.IsFiniteLocallyFree]
    (e : Nonempty ((Modules.tensorPullback (pullback.fst f g)).obj E ≅
      (Modules.tensorPullback (pullback.snd f g)).obj N))
    {T' : Scheme.{u}} (h : T' ⟶ T) :
      IsIso (Modules.moduleBaseChangeMap (pullback.snd f g)
        (pullback.snd (pullback.snd f g) h) h (pullback.fst (pullback.snd f g) h)
        pullback.condition
          ((Modules.tensorPullback (pullback.fst f g)).obj (Modules.dual E))) := by
  have : (Modules.dual E).IsFiniteLocallyFree := Modules.IsFiniteLocallyFree.dual E
  have : (Modules.dual N).IsFiniteLocallyFree := Modules.IsFiniteLocallyFree.dual N
  obtain ⟨i⟩ := e
  obtain ⟨dE⟩ := tensorPullback_dual_iso (pullback.fst f g) E
  obtain ⟨dN⟩ := tensorPullback_dual_iso (pullback.snd f g) N
  let d := dE ≪≫ ((Modules.dualFunctor (pullback f g)).mapIso i.op).symm ≪≫ dN.symm
  exact picard_pullback_base_change_primal f hO (Modules.dual E) g (Modules.dual N) ⟨d⟩ h
end AlgebraicGeometry.Scheme
