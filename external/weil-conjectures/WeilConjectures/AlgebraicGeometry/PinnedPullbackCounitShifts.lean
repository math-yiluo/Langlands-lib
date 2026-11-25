/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift

/-! # Shifts compatible with the composition-pinned pullback counits
Source: Stacks Project, Tags 08HY and 0D5S.
(blueprint: lem-pc-pinned-pullback-counit-shifts). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
noncomputable section
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency.types false

/-- The left-derived counit selected by the composition theorem.
Source: Stacks Project, Tag 0D5S
(blueprint: lem-pc-ringed-spaces-derived-pullback-composition).
(blueprint: lem-pc-pinned-pullback-counit-shifts)
-/
abbrev pinnedPullbackCounit
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) f

/-- The composition-pinned left-derived counits admit compatible integer shifts.
Source: Stacks Project, Tags 0D5S and 08HY; derived universal property.
(blueprint: lem-pc-pinned-pullback-counit-shifts).
Proof: for each f, compare the two functors obtained by shifting before and after
Lf*. Both are left derived functors of the corresponding shifted termwise tensor
pullback. Shift is an equivalence and preserves quasi-isomorphisms, so the
left-derived universal property supplies a unique comparison compatible with the
specified counit. Applying the same construction to the inverse shift proves
invertibility. Uniqueness gives the zero and addition laws, since the termwise
shift comparisons satisfy them. The compatibility equation is exactly
NatTrans.CommShift for the specified counit. Do this for every morphism; no
flatness, boundedness or geometric hypothesis is required. -/
theorem exists_pinned_pullback_counit_shifts
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive] :
    ∃ s : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), (derivedPullback.{u, w} f).CommShift ℤ,
      ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
        letI := s f
        NatTrans.CommShift (pinnedPullbackCounit.{u, w} f) ℤ  := by
  classical
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  have h : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      ∃ s : (derivedPullback.{u, w} f).CommShift ℤ,
        letI := s
        NatTrans.CommShift (pinnedPullbackCounit.{u, w} f) ℤ := by
    intro X Y f
    have hL := (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w}))) f
    exact Functor.rightKanExtension_coherentShift _ DerivedCategory.Qh
      (derivedPullback.{u, w} f) (pinnedPullbackCounit.{u, w} f)
      hL.isRightKanExtension
  refine ⟨fun f ↦ Classical.choose (h f), ?_⟩
  intro X Y f
  exact Classical.choose_spec (h f)

end AlgebraicGeometry
