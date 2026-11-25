/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullback
import WeilConjectures.AlgebraicGeometry.Structure.StructureSheafCohomologyPullbackCompositionPointwise

/-! Composition law for pullback on structure-sheaf cohomology.
(blueprint: lem-sc-structure-sheaf-cohomology-pullback-composition)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Pullback on structure-sheaf cohomology reverses composition.
Source: Stacks Project, Cohomology of Sheaves, Section 01F7, equation-functorial
and Remark 01FB.

Proof: Write Lf and Lg for the exact inverse images and Lfg for inverse image
along f ≫ g. There is a canonical comparison alpha : Lfg ≅ Lg ⋙ Lf, obtained from
the equality of composite direct images by uniqueness of left adjoints. Write af,
ag and afg for the adjoints of the additive structure maps, and cf, cg and cfg for
the constant-integer-sheaf comparisons Z_X → Lf(Z_Y), Z_Y → Lg(Z_Z) and
Z_X → Lfg(Z_Z). Compatibility with the adjunction units and the formula for the
structure map of a composite give
  afg = alpha at O_Z ; Lf(ag) ; af.
The construction of the constant comparison by uniqueness of left adjoints gives
  cfg ; alpha at Z_Z = cf ; Lf(cg).
For x : Ext Z_Z O_Z n, unfold H.mapFunctor and H.map: the pullback of x is
cfg ; Lfg(x) ; afg. Substitute the first equality and use naturality of alpha on
Ext to move alpha from the coefficient object to Z_Z. Substitute the second equality.
Functoriality of exact-functor maps on Ext and associativity of Yoneda products now
give cf ; Lf(cg ; Lg(x) ; ag) ; af, which is f*(g*(x)). This proves equality
pointwise, hence equality of additive homomorphisms. The argument includes degree
zero, either identity morphism, and empty schemes without extra hypotheses.
(blueprint: lem-sc-structure-sheaf-cohomology-pullback-composition) -/
theorem structureSheafCohomologyPullback_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    structureSheafCohomologyPullback (f ≫ g) n =
      (structureSheafCohomologyPullback f n).comp
        (structureSheafCohomologyPullback g n) := by
  ext x
  exact structureSheafCohomologyPullback_comp_apply f g n x

end AlgebraicGeometry.Scheme
