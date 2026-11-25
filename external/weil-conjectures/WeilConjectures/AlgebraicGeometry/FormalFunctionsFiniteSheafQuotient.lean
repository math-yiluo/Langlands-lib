/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FormalFunctionsFinitePullback
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.QuotientBaseChangeIdeal
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitQuotient
import WeilConjectures.AlgebraicGeometry.FormalFunctionsFiniteSheafQuotientCore

/-! # Sheaf quotients on the finite fibres

Source: Stacks Project, Tag 02OD, finite-level identifications, and Tag 04CJ (1).
(blueprint: lem-weil-pbc-formal-functions-finite-sheaf-quotient)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

namespace AlgebraicGeometry

/-- The finite fibre immersion is closed, and its direct image of the pulled-back module
is the quotient of the local pullback by the corresponding power of the extended ideal.
The quotient equation specifies the isomorphism uniquely, since the quotient projection
is an epimorphism. No cohomology or transition compatibility is asserted here.

Source: Stacks Project, Tag 02OD, finite-level identifications; Tag 04CJ (1).
(blueprint: lem-weil-pbc-formal-functions-finite-sheaf-quotient)
Proof: Paste the two base-change squares to identify the finite fibre over the local
base change with the pullback of Spec(A/m^(n+1)) into Spec(A). This is a closed immersion.
The quotient-base-change ideal computation identifies its kernel with the extension of
m^(n+1). Extension commutes with products, so this is the (n+1)-st power of J.
On each affine open, the sheaf power inclusion in formalModuleQuotient is the inclusion
of this ideal power; hence its product with F' is the kernel of the closed-immersion
unit. Apply closedImmersion_unit_quotient to obtain the cokernel isomorphism. Identify
the iterated tensor pullback of F with its pullback to the finite fibre by uniqueness
of left adjoints. The adjunction-unit equation identifies the composite unit with
formalFunctionsFiniteFMap. The cokernel universal property gives the displayed equation;
the epimorphism property of its projection also gives uniqueness. The argument works
for every module, including the zero module, and every n, including n = 0. -/
theorem formalFunctions_finite_sheaf_quotient {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules) (y : Y) :
    let F' := (Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F
    let J := (Scheme.IdealSheafData.ofIdealTop
      ((maximalIdeal (Y.presheaf.stalk y)).map
        (Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv.hom)).comap
          (pullback.fst (Y.fromSpecStalk y) f)
    ∀ n : ℕ, IsClosedImmersion (formalFunctionsFiniteι f y n) ∧
      ∃ e : formalModuleQuotient J (n + 1) F' ≅
          (Scheme.Modules.pushforward (formalFunctionsFiniteι f y n)).obj
            ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F),
        formalModuleQuotientπ J (n + 1) F' ≫ e.hom =
          formalFunctionsFiniteFMap f y F n := by
  dsimp
  intro n
  refine ⟨formalFunctionsFiniteι_isClosedImmersion f y n, ?_⟩
  exact formalFunctionsFinite_sheaf_quotient_iso f F y n

end AlgebraicGeometry
