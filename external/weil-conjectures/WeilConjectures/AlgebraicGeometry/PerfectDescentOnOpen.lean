/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.Picard.TwistedDescent

/-! # The open-subscheme predicate for perfect-complex descent

Source: Stacks Project, Tag 09RF, induction on quasi-compact opens.
(blueprint: def-pc-perfect-descent-on-open).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Descent holds on the open `U` if it holds for every presentation of that open by an
open immersion into `Xi`. Quantifying over presentations allows the top open to be
presented by the identity of `Xi`, without transporting the final theorem through
`Xi.topIso`. All objects and pullback maps in this predicate are explicitly fixed.
Source: Stacks Project, Tag 09RF, induction on quasi-compact opens
(blueprint: def-pc-perfect-descent-on-open). -/
def PerfectDescentOnOpen
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cocone R) (i : I) (Xi : Scheme.{u}) (s : Xi ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (U : Xi.Opens) : Prop :=
  ∀ (Z : Scheme.{u}) (f : Z ⟶ Xi) [IsOpenImmersion f], f.opensRange = U →
    let t := f ≫ s
    ∀ (E : schemeDerivedCategory (pullback t (Spec.map (c.ι.app i)))),
      (pullback t (Spec.map (c.ι.app i))).IsPerfect E →
    ∃ (j : I) (hij : i ≤ j)
      (Ej : schemeDerivedCategory (pullback t (Spec.map (R.map (homOfLE hij))))),
      (pullback t (Spec.map (R.map (homOfLE hij)))).IsPerfect Ej ∧
      Nonempty ((derivedPullback (baseChangeMap t
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (c.ι.app i)))
          (Over.homMk (Spec.map (c.ι.app j))
            (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])))).obj Ej ≅ E)

end AlgebraicGeometry
