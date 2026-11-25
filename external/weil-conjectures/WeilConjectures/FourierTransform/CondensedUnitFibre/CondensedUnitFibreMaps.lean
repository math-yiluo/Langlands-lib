/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.FiniteEtaleStalk
public import WeilConjectures.WeilObject.Sheaf.StalkUnit

/-!
# Canonical unit maps on fibres for a condensed coefficient ring

The constructions are the coefficient unit, its pullback comparison, the counit components,
and the base-change exchange. They retain the coefficient ring as a parameter so their
categorical identities can be proved before specializing the coefficients.

Source: blueprint latest, `sec-fourier-transform/sk-lem-as-properties/lem-fd-as-trace.proof.md`,
first paragraph (blueprint: def-fd-condensed-unit-fibre-maps).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedUnitFibre

/-- The coefficient unit, using the recorded pulled-back condensed ring.
Source: blueprint finite-fibre paragraph (blueprint: def-fd-condensed-unit-fibre-maps). -/
abbrev unit (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u}) :=
  Mod.regular (condensedRingObj Λ T)

/-- The canonical unit comparison, in the direction from the pullback to the unit.
Source: blueprint finite-fibre paragraph (blueprint: def-fd-condensed-unit-fibre-maps). -/
def unitPullback (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {T U : Scheme.{u}} (a : T ⟶ U) :
    (upperStar Λ a).obj (unit Λ U) ≅ unit Λ T :=
  (Functor.Monoidal.εIso (upperStar Λ a)).symm

/-- Direct image of the coefficient unit.
Source: blueprint finite-fibre paragraph (blueprint: def-fd-condensed-unit-fibre-maps). -/
abbrev push (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y X : Scheme.{u}} (f : Y ⟶ X) :=
  (lowerStar Λ f).obj (unit Λ Y)

/-- The counit projection followed by the canonical coefficient-unit comparison.
Source: blueprint finite-fibre paragraph (blueprint: def-fd-condensed-unit-fibre-maps). -/
@[irreducible] def component (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y X P : Scheme.{u}} (f : Y ⟶ X)
    (x : P ⟶ X) (y : P ⟶ Y) (h : y ≫ f = x) :
    (upperStar Λ x).obj (push Λ f) ⟶ unit Λ P :=
  stalkLowerStarProj Λ h (unit Λ Y) ≫
    (unitPullback Λ y).hom

/-- The coefficient-unit exchange attached to a commutative square. For an isomorphism
square this is the induced Weil structure; for maps of covers it is pullback of functions.
Source: blueprint finite-fibre paragraph (blueprint: def-fd-condensed-unit-fibre-maps). -/
def exchange (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y X Y' X' : Scheme.{u}}
    {f : Y ⟶ X} {f' : Y' ⟶ X'} {a : Y' ⟶ Y} {b : X' ⟶ X}
    (sq : CommSq a f' f b) :
    (upperStar Λ b).obj (push Λ f) ⟶ push Λ f' :=
  (lowerStarBaseChange Λ sq).app (unit Λ Y) ≫
    (lowerStar Λ f').map (unitPullback Λ a).hom


/-- The canonical Weil structure on the direct image of the coefficient unit, for a square of
isomorphisms: the base-change exchange followed by the direct image of the coefficient-unit
comparison. Its forward map is `exchange Λ sq`.
Source: blueprint finite-fibre paragraph, induced Weil structure
(blueprint: def-fd-condensed-unit-fibre-maps). -/
def weil (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y X : Scheme.{u}} {f : Y ⟶ X} {a : Y ⟶ Y} {b : X ⟶ X}
    [IsIso a] [IsIso b] (sq : CommSq a f f b) :
    (upperStar Λ b).obj (push Λ f) ≅ push Λ f :=
  (asIso (lowerStarBaseChange Λ sq)).app (unit Λ Y) ≪≫
    (lowerStar Λ f).mapIso (unitPullback Λ a)

/-- The local return operator of the induced coefficient-unit Weil structure.
Source: blueprint local Frobenius clause (blueprint: def-fd-condensed-unit-fibre-maps). -/
def returnEnd (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {k : Type u} [Field k] [IsSepClosed k]
    {Y X : Scheme.{u}} {f : Y ⟶ X} {a : Y ⟶ Y} {b : X ⟶ X}
    (sq : CommSq a f f b) (σ : Spec (.of k) ⟶ Spec (.of k))
    (x : Spec (.of k) ⟶ X) (hx : x ≫ b = σ ≫ x) :
    End ((upperStar Λ x).obj (push Λ f)) :=
  End.of <| (pointComparison Λ
    (upperStarIsoIdOfIsSepClosed Λ σ) b hx).hom.app
      (push Λ f) ≫
    (upperStar Λ x).map (exchange Λ sq)



end WeilConjectures.CondensedUnitFibre
