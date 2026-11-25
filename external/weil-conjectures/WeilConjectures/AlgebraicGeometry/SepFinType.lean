/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Separated schemes of finite type over a field

For a field `k`, this file defines the category `AlgebraicGeometry.SepFinType k` of separated
`k`-schemes of finite type, as a full subcategory of `Over (Spec k)`, and the class
`AlgebraicGeometry.SepFinType.openImmersion` of open immersions between them.

## Main definitions

- `AlgebraicGeometry.SepFinType`: the separated `k`-schemes of finite type, as a full
  subcategory of `Over (Spec k)`, and `AlgebraicGeometry.SepFinType.mk`, `homMk`.
- `AlgebraicGeometry.SepFinType.openImmersion`: the open immersions in `SepFinType k`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme

section SepFinType

variable (k : Type u) [Field k]

/-- The property of a `k`-scheme of being separated and of finite type over `k`. -/
def sepFinType : ObjectProperty (Over (Spec (.of k))) :=
  fun X ↦ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom ∧ IsSeparated X.hom

/-- The separated `k`-schemes of finite type, as a full subcategory of `Over (Spec k)`: the
schemes on which the bounded constructible six functors are defined. -/
abbrev SepFinType := (sepFinType k).FullSubcategory

variable {k}

instance (X : SepFinType k) : LocallyOfFiniteType X.obj.hom := X.property.1
instance (X : SepFinType k) : QuasiCompact X.obj.hom := X.property.2.1
instance (X : SepFinType k) : IsSeparated X.obj.hom := X.property.2.2

/-- A separated `k`-scheme of finite type as an object of `SepFinType k`. -/
noncomputable abbrev SepFinType.mk (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] : SepFinType k :=
  ⟨X, ⟨inferInstance, inferInstance, inferInstance⟩⟩

/-- A morphism of separated `k`-schemes of finite type as a morphism of `SepFinType k`. -/
noncomputable abbrev SepFinType.homMk {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] (f : X ⟶ Y) : SepFinType.mk X ⟶ SepFinType.mk Y :=
  ObjectProperty.homMk f

/-- The open immersions of separated `k`-schemes of finite type. -/
def SepFinType.openImmersion : MorphismProperty (SepFinType k) :=
  fun _ _ f ↦ IsOpenImmersion f.hom.left

instance : (SepFinType.openImmersion (k := k)).ContainsIdentities where
  id_mem X := inferInstanceAs (IsOpenImmersion (𝟙 X.obj.left))

instance {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (j : X ⟶ Y) [IsOpenImmersion j.left] :
    Fact (SepFinType.openImmersion (SepFinType.homMk j)) :=
  ⟨inferInstanceAs (IsOpenImmersion j.left)⟩

instance {X Y : SepFinType k} (j : X ⟶ Y) [h : Fact (SepFinType.openImmersion j)] :
    IsOpenImmersion j.hom.left :=
  h.out

end SepFinType

end AlgebraicGeometry
