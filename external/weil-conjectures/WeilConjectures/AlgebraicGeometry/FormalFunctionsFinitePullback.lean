/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FormalFunctionsLocalStalkComparison

/-! # Finite-level pullback of a local cohomology class

Source: Stacks Project, Tag 02OD, factorization of the infinitesimal neighbourhoods;
Tags 01F7 and 01FB, functoriality of cohomology.
(blueprint: def-weil-pbc-formal-functions-finite-pullback)
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

namespace AlgebraicGeometry
noncomputable section

/-- The map from the infinitesimal fibre to the local base change, by pullback pasting.
Source: Stacks Project, Tag 02OD, factorization through Spec O_y.
(blueprint: def-weil-pbc-formal-functions-finite-pullback) -/
def formalFunctionsFiniteι {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (n : ℕ) :
    formalFibre f y n ⟶ pullback (Y.fromSpecStalk y) f :=
  pullback.lift
    (pullback.fst (formalFibreBaseMap Y y n) f ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (formalFibreIdeal Y y n))))
    (formalFibreι f y n)
    (by simpa [formalFibreBaseMap, formalFibreι, Category.assoc] using
      (pullback.condition (f := formalFibreBaseMap Y y n) (g := f)))

/-- The finite-level map has the expected projection to X.
Source: Stacks Project, Tag 02OD; the second pullback projection.
(blueprint: def-weil-pbc-formal-functions-finite-pullback) -/
theorem formalFunctionsFiniteι_snd {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (n : ℕ) :
    formalFunctionsFiniteι f y n ≫ pullback.snd (Y.fromSpecStalk y) f =
      formalFibreι f y n := by
  simp [formalFunctionsFiniteι]

/-- The h-map from F' to the direct image of F_n, obtained by adjunction from
F → i_n*F_n. This specifies the map without choosing a module isomorphism.
Source: Stacks Project, Tags 02OD and 01F7.
(blueprint: def-weil-pbc-formal-functions-finite-pullback) -/
def formalFunctionsFiniteFMap {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    (F : X.Modules) (n : ℕ) :
    (Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F ⟶
      (Scheme.Modules.pushforward (formalFunctionsFiniteι f y n)).obj
        ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F) :=
  ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
    (pullback.snd (Y.fromSpecStalk y) f))).homEquiv F _).symm
    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
        (formalFibreι f y n))).unit.app F ≫
      (Scheme.Modules.pushforwardCongr (formalFunctionsFiniteι_snd f y n).symm).hom.app
        ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F) ≫
      (Scheme.Modules.pushforwardComp (formalFunctionsFiniteι f y n)
        (pullback.snd (Y.fromSpecStalk y) f)).inv.app
          ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F))

/-- The canonical finite-level pullback on the underlying cohomology groups.
Source: Stacks Project, Tags 02OD and 01FB.
(blueprint: def-weil-pbc-formal-functions-finite-pullback) -/
def formalFunctionsFinitePullback {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    (F : X.Modules) (p n : ℕ) :
    formalFunctionsLocalCohomology f y F p →+ formalFibreCohomologyLocal f y F p n :=
  (Scheme.Modules.moduleCohomologyFMap (formalFunctionsFiniteι f y n)
    (formalFunctionsFiniteFMap f y F n) p).hom

end
end AlgebraicGeometry
