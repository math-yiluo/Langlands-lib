/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit

/-! # The canonical section map through a factorization of scheme maps

## References

* Stacks Project, Tag 01CA, associativity and functoriality of tensor pullback
* Stacks Project, Tag 01CA, tensor associativity
-/

@[expose] public section

noncomputable section
universe u
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- Pull a section along v and identify the iterated pullback with h* M.

This is the adjunction unit on sections followed by the canonical composition
comparison. It is an explicit construction. Keeping this section map irreducible
avoids unfolding the concrete scheme pullback and sheafification while matching
two occurrences of the same transport. -/
def pullbackSectionFactorization
    {X Y Z : Scheme.{u}} (g : Y ⟶ X) (h : Z ⟶ X) (v : Z ⟶ Y)
    (hv : v ≫ g = h) (M : X.Modules) :
    Γ((pullback g).obj M, ⊤) → Γ((pullback h).obj M, ⊤) :=
  fun x ↦ Hom.app (pullbackCompOfEq v g h hv M).hom ⊤
    (pullbackΓ v ((pullback g).obj M) x)

attribute [irreducible] pullbackSectionFactorization

end AlgebraicGeometry.Scheme.Modules
