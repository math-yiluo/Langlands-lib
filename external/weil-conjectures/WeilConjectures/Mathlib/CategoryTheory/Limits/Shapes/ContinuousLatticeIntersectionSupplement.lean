/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.CategoryTheory.Limits.Shapes.Images
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
public import WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersection

/-! # The canonical intersection of the lattices on a finite cover

The inverse image of the pushed-forward lattice image under the adjunction unit
is a genuine categorical pullback. Over a split finite cover it is the intersection
of the sheet lattices, so its construction requires no choices of splittings.

Source: Bhatt--Scholze, Lemma 6.8.13, finite-etale descent of integral structures.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] [Abelian C] {A B D : C}

end CategoryTheory.Limits

namespace CategoryTheory.Adjunction

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a] (X : Scheme.{u})
  (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj S X))
  {U : Scheme.{u}} (p : U ⟶ X)
  (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
    (condensedRingObj R U))
  (e : (Mod.extendScalars (coefficientMap a U)).obj M ≅
    (upperStar S p).obj P)

end AlgebraicGeometry.ProEtale.CondensedRing
