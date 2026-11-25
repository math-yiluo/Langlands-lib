/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.AlgebraicGeometry.OpenPerfectModelTransport

/-! # Perfectness detected on open neighbourhoods

Source: Stacks Project, Tag 08CM, definition-perfect
(blueprint: lem-pc-perfect-of-open-pullbacks).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exact restriction to an open subscheme computes its derived tensor pullback. -/
private theorem open_pullback_iso (S : Scheme.{u}) (U : S.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))] :
    let A : SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U) ⥤
        SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
      (Scheme.Modules.overEquiv U).functor
    letI : A.Additive := Functor.additive_of_preserves_binary_products _
    let R := SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U
    letI : PreservesFiniteLimits (R ⋙ A) := comp_preservesFiniteLimits _ _
    letI : PreservesFiniteColimits (R ⋙ A) := comp_preservesFiniteColimits _ _
    Nonempty (derivedPullback U.ι ≅ (R ⋙ A).mapDerivedCategory) := by
  let A : SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    (Scheme.Modules.overEquiv U).functor
  have : A.Additive := Functor.additive_of_preserves_binary_products _
  let R := SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U
  have : PreservesFiniteLimits (R ⋙ A) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (R ⋙ A) := comp_preservesFiniteColimits _ _
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    F, hF, hFmap, hFadd, ε, hL, htri, hK⟩ :=
    derivedPullback_spec U.ι
  have h : F = Scheme.Modules.tensorPullback U.ι :=
    CategoryTheory.Functor.ext hF (fun M N a ↦ hFmap a)
  subst F
  let T : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    Scheme.Modules.tensorPullback U.ι
  let η : T ≅ Scheme.Modules.restrictFunctor U.ι :=
    (Scheme.Modules.nonempty_tensorPullbackAdjunction U.ι).some.leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction U.ι) ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
  let θ : R ⋙ A ≅ T := Scheme.Modules.overFunctorEquiv U ≪≫ η.symm
  have : PreservesFiniteLimits T := preservesFiniteLimits_of_natIso θ
  have : PreservesFiniteColimits T := preservesFiniteColimits_of_natIso θ
  let W := HomotopyCategory.quasiIso
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (.up ℤ)
  have : (derivedPullback U.ι).IsLeftDerivedFunctor ε W := hL
  have : T.mapDerivedCategory.IsLeftDerivedFunctor T.mapDerivedCategoryFactorsh.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ T.mapDerivedCategoryFactorsh
  let i : derivedPullback U.ι ≅ T.mapDerivedCategory :=
    Functor.leftDerivedUnique T.mapDerivedCategory (derivedPullback U.ι) ε
      T.mapDerivedCategoryFactorsh.hom W
  exact ⟨i ≪≫ (Functor.mapDerivedCategoryNatIso θ).symm⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Perfectness is local for derived pullback along open immersions.
Source: Stacks Project, Tag 08CM, definition-perfect; Tag 0A1H, locality sentence.
Proof: for x choose U containing x on which the derived restriction is perfect.
Choose a strictly perfect representative near the point of U corresponding to x.
An open of U is an open V of S contained in U. Exact open restriction agrees with
its left derived functor, by uniqueness of left derived functors. The equivalences
between module sheaves on open subschemes and on localized sites identify successive
restrictions with restriction to V. They preserve finite free modules, their retract
maps and zero terms. Transport the local representative and its isomorphism across
these equivalences. This gives precisely the witness at x in S.IsPerfect K.
The empty scheme is vacuous and no uniform bound or quasi-compactness is required.
(blueprint: lem-pc-perfect-of-open-pullbacks). -/
theorem perfect_of_open_pullbacks
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens), HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    {S : Scheme.{u}} (K : schemeDerivedCategory S)
    (h : ∀ x : S, ∃ U : S.Opens, x ∈ U ∧
      Scheme.IsPerfect U.toScheme ((derivedPullback U.ι).obj K)) :
    Scheme.IsPerfect S K := by
  intro x
  obtain ⟨U, hxU, hU⟩ := h x
  obtain ⟨o⟩ := open_pullback_iso S U
  exact Scheme.local_perfect_of_openRestriction_iso S U K
    ((derivedPullback U.ι).obj K) hU (o.app K).symm x hxU

end AlgebraicGeometry
