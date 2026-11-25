/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import Mathlib.AlgebraicGeometry.FunctionField

/-!

# Normality of open subschemes

A nonempty open subscheme of a normal scheme is normal
(`AlgebraicGeometry.IsNormalScheme.of_isOpenImmersion`): it is integral, and its local rings are
those of the ambient scheme. A nonzero global function on an integral scheme stays nonzero on a
nonempty open subscheme (`AlgebraicGeometry.Scheme.Hom.appTop_ne_zero_of_isOpenImmersion`).

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- **A nonempty open subscheme of a normal scheme is normal.** -/
theorem IsNormalScheme.of_isOpenImmersion {V X : Scheme.{u}} (g : V ⟶ X) [IsOpenImmersion g]
    [Nonempty V] (hX : IsNormalScheme X) : IsNormalScheme V := by
  have := hX.1
  refine ⟨isIntegral_of_isOpenImmersion g, fun v ↦ ?_⟩
  obtain ⟨h₁, h₂⟩ := hX.2 (g v)
  let e : X.presheaf.stalk (g v) ≃+* V.presheaf.stalk v :=
    (asIso (g.stalkMap v)).commRingCatIsoToRingEquiv
  exact ⟨e.symm.injective.isDomain _, (IsIntegrallyClosed.of_equiv e)⟩

/-- A nonzero global function on an integral scheme restricts to a nonzero function on a
nonempty open subscheme. -/
theorem Scheme.Hom.appTop_ne_zero_of_isOpenImmersion {V X : Scheme.{u}} (g : V ⟶ X)
    [IsOpenImmersion g] [Nonempty V] [IsIntegral X] {h : Γ(X, ⊤)} (hh : h ≠ 0) :
    g.appTop h ≠ 0 := by
  have := isIntegral_of_isOpenImmersion g
  obtain ⟨v⟩ := ‹Nonempty V›
  intro h0
  have h1 : g.stalkMap v (X.presheaf.germ ⊤ (g v) trivial h) = 0 := by
    rw [Scheme.Hom.germ_stalkMap_apply]
    simpa [Scheme.Hom.appTop] using congrArg (V.presheaf.germ ⊤ v trivial) h0
  have h2 : X.presheaf.germ ⊤ (g v) trivial h = 0 :=
    (asIso (g.stalkMap v)).commRingCatIsoToRingEquiv.injective (by rw [map_zero]; exact h1)
  exact hh (germ_injective_of_isIntegral X (U := ⊤) (g v) trivial (by rw [h2, map_zero]))

end AlgebraicGeometry
