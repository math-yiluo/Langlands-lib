/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided

/-!
# Derived pullback preserves the canonical tensor symmetry

Source: Stacks Project, Tag 06YU; the symmetry conjugation in step 6 of
`lem-asd-compact-projection-exchange` (auxiliary; not a blueprint node).
-/

@[expose] public section

universe u' u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize

/-- Exact derived pullback preserves the canonical signed tensor symmetry.
Source: Stacks Project, Tag 06YU, and step 6 of `lem-asd-compact-projection-exchange`
(auxiliary; not a blueprint node).

Proof: the oplax tensor structure of inverse image on sheaves respects the ordinary
symmetry by doctrinal adjunction from its lax braided right adjoint. Apply it degreewise
and totalize: on bidegree `(p,q)` both routes use the same swap with scalar `(-1)^(p*q)`.
Pullback preserves flat sheaves, hence K-flat representatives with flat terms. Compute
its derived tensor comparison on these representatives and descend the preceding chain
identity through localization. Every derived object is isomorphic to such a representative;
naturality of the comparisons and symmetry then gives the equation for arbitrary `K,M`.
The upstream theorem `leftDerivedUpperStar_map_braiding_hom_δ` supplies this argument for
the derived braiding; `derivedTensorSymmetry` packages exactly that same braiding. -/
theorem derivedPullback_tensorSymmetry
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (g : X ⟶ Y)
    (K M : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    L((g)^*[ModuleCat.{u + 1} Λ]).map
        (((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) Y).hom.app K).app M) ≫
      ((leftDerivedUpperStarTensorComparison _ g).app M).app K =
    ((leftDerivedUpperStarTensorComparison _ g).app K).app M ≫
      ((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) X).hom.app
        (L((g)^*[ModuleCat.{u + 1} Λ]).obj K)).app
          (L((g)^*[ModuleCat.{u + 1} Λ]).obj M) := by
  exact leftDerivedUpperStar_map_braiding_hom_δ (ModuleCat.{u + 1} Λ) g K M

end AlgebraicGeometry.Etale
