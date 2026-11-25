/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import WeilConjectures.Algebra.Homology.ShortComplex.MapHomologyIsoComp

/-!
# The structure isomorphism of a homology object of algebras

Let `G` be an exact additive endofunctor of an abelian category `C`. The structure
isomorphisms of the objects of `IsoAlgebra G` form a natural isomorphism
`CategoryTheory.Endofunctor.IsoAlgebra.strNatIso : forget G ⋙ G ≅ forget G`.

The structure isomorphism of the homology of a short complex `S` of algebras is the map induced
on homology by the structure isomorphisms of the terms of `S`, read through the identifications
`forget (H S) ≅ H (forget S)` and `G (H (forget S)) ≅ H (G (forget S))`
(`CategoryTheory.Endofunctor.IsoAlgebra.homologyMap_mapNatTrans_strNatIso_hom`).
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] (G : C ⥤ C)

variable [Abelian C] [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- **The structure isomorphism of a homology object.** For a short complex `S` of algebras of
an exact functor `G`, the structure isomorphism of `H S` is the map induced on homology by the
structure isomorphisms of the terms of `S`:
```
G (H (forget S)) ≅ H (G (forget S)) --H(str)--> H (forget S) ≅ forget (H S)
```
-/
theorem homologyMap_mapNatTrans_strNatIso_hom (S : ShortComplex (IsoAlgebra G)) :
    ((S.map (forget G)).mapHomologyIso G).inv ≫
        ShortComplex.homologyMap (S.mapNatTrans (strNatIso G).hom) ≫
          (S.mapHomologyIso (forget G)).hom =
      G.map (S.mapHomologyIso (forget G)).hom ≫ S.homology.str.hom := by
  rw [ShortComplex.homologyMap_mapNatTrans, ShortComplex.mapHomologyIso_comp]
  simp

end CategoryTheory.Endofunctor.IsoAlgebra
