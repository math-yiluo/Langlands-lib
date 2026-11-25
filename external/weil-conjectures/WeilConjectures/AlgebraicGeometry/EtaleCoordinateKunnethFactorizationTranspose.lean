/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleCoordinateTraceData
import WeilConjectures.AlgebraicGeometry.EtaleCoordinateKunnethRouteEquality

/-! # The transpose computation for the coordinate Kunneth factorization

This is the mate calculation used in the proof of the coordinate Kunneth
factorization.  It isolates the comparison of the two pullback-counit
transposes from the final cancellation by the derived adjunction.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.CoordinateTrace

variable (A : Type (u + 1)) [CommRing A]

/-- The two coordinate routes have the same transpose along `pull f ⊣ push f`.
Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, first triangle, coordinate interchange;
Stacks Tags 07A7, 0B56 and 0D6E.

Proof: expand the two projection maps by their adjunction-mate formulas.  Naturality
of the derived tensor comparison moves the first pullback through the tensor, while
the mate equations for `exchange1` and `exchange2` identify the two base-change
routes.  The tensor comparison for the pullback square then identifies the resulting
maps, and the counit equation for `directComparison` identifies their direct-image
targets.  This is the pullback-counit calculation; the final cancellation by the
adjunction is performed by `coordinateKunnethFactorization_route_eq`.
(auxiliary; not a blueprint node). -/
theorem coordinateKunnethFactorization_transpose [Finite A] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] (L : DerivedCategoryModule A Y)
    (M : DerivedCategoryModule A X) :
    (pull A f).map
        ((orderedProjectionIso A f ((push A f).obj M) ((pull A f).obj L)).hom ≫
          (push A f).map (comparison A f L M).inv ≫
          (directComparison A f).hom.app _) ≫
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).counit.app _ =
      (pull A f).map
          (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app M).app
              ((push A f).obj ((pull A f).obj L)) ≫
            (push A f).map
              (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
                  (exchange1 A f ((pull A f).obj L)).hom ≫
                (orderedProjectionIso A (pullback.fst f f) M
                  ((pull A (pullback.snd f f)).obj ((pull A f).obj L))).hom)) ≫
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).counit.app _ := by
  rw [coordinateKunnethFactorization_route_eq A f L M]

end AlgebraicGeometry.Etale.CoordinateTrace
