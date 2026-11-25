/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Bundling an S-scheme retains local finite type of its structure map. -/
instance Scheme.locallyOfFiniteType_asOver_hom (X S : Scheme.{u}) [X.Over S]
    [LocallyOfFiniteType (X ↘ S)] : LocallyOfFiniteType (X.asOver S).hom :=
  ‹LocallyOfFiniteType (X ↘ S)›

/-- Bundling an S-scheme retains quasi-compactness of its structure map. -/
instance Scheme.quasiCompact_asOver_hom (X S : Scheme.{u}) [X.Over S]
    [QuasiCompact (X ↘ S)] : QuasiCompact (X.asOver S).hom :=
  ‹QuasiCompact (X ↘ S)›

/-- Bundling an S-scheme retains separatedness of its structure map. -/
instance Scheme.isSeparated_asOver_hom (X S : Scheme.{u}) [X.Over S]
    [IsSeparated (X ↘ S)] : IsSeparated (X.asOver S).hom :=
  ‹IsSeparated (X ↘ S)›

variable {S X Y X' Y' : Scheme.{u}}
  [X.Over S] [Y.Over S] [X'.Over S] [Y'.Over S]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  [f.IsOver S] [g.IsOver S] [f'.IsOver S] [g'.IsOver S]

/-- A commutative square of morphisms over a scheme, bundled in its over category. -/
theorem _root_.CategoryTheory.CommSq.asOver (sq : CommSq g' f' f g) (S : Scheme.{u})
    [X.Over S] [Y.Over S] [X'.Over S] [Y'.Over S]
    [f.IsOver S] [g.IsOver S] [f'.IsOver S] [g'.IsOver S] :
    CommSq (g'.asOver S) (f'.asOver S) (f.asOver S) (g.asOver S) :=
  ⟨Over.OverMorphism.ext sq.w⟩

/-- A cartesian square of morphisms over a scheme, bundled in its over category. -/
theorem _root_.CategoryTheory.IsPullback.asOver (sq : IsPullback g' f' f g) (S : Scheme.{u})
    [X.Over S] [Y.Over S] [X'.Over S] [Y'.Over S]
    [f.IsOver S] [g.IsOver S] [f'.IsOver S] [g'.IsOver S] :
    IsPullback (g'.asOver S) (f'.asOver S) (f.asOver S) (g.asOver S) :=
  IsPullback.of_map (Over.forget S) (Over.OverMorphism.ext sq.w) sq

end AlgebraicGeometry
