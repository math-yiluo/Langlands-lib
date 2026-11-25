/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
module

import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

public import WeilConjectures.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Preserves
public import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
public import Mathlib.AlgebraicGeometry.Sites.Pretopology
public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Sieves
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Limits.Shapes.DisjointCoproduct
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.MonoCoprod
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
public import Mathlib.CategoryTheory.Sites.SheafOfTypes
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Sites.CoproductSheafCondition
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.CategoryTheory.Sites.IsSheafFor
public import WeilConjectures.AlgebraicGeometry.ProEtale.Flat.QuasiCompactCover
public import Mathlib.CategoryTheory.Extensive

/-!
# The pro-étale site of a scheme

-/

@[expose] public section

universe u

open CategoryTheory MorphismProperty

namespace AlgebraicGeometry.Scheme

namespace ProEt

variable (X : Scheme.{u})

def zariskiTopology : GrothendieckTopology X.ProEt :=
  X.smallGrothendieckTopology (P := @IsOpenImmersion) (Q := @WeaklyEtale)



instance precoverageHasIsos : (precoverage X).HasIsos :=
  instHasIsosPrecoverage_weilConjectures.{u} X

instance precoverageStableUnderComposition : (precoverage X).IsStableUnderComposition :=
  instIsStableUnderCompositionPrecoverage_weilConjectures.{u} X

instance precoverageStableUnderBaseChange : (precoverage X).IsStableUnderBaseChange :=
  instIsStableUnderBaseChangePrecoverage_weilConjectures.{u} X

variable {S : Scheme.{u}}

instance {X Y : S.ProEt} (f : X ⟶ Y) : WeaklyEtale f.left :=
  have : WeaklyEtale (f.left ≫ Y.hom) := by simp [X.prop]
  .of_comp _ Y.hom

end ProEt

end AlgebraicGeometry.Scheme
