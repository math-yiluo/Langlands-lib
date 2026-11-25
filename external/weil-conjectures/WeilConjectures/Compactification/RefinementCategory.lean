/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Category.Basic
public import WeilConjectures.Compactification.Defs

/-!

# Refinements of compactifications

A refinement of a compactification `d` of `f : X ⟶ Y` by a compactification `c` of `f` is a
morphism `c.Z ⟶ d.Z` of the ambient schemes commuting both with the open immersions of `X`
and with the structure morphisms to `Y`. Such a morphism is automatically proper, since it is
a morphism over `Y` whose source is proper over `Y` and whose target is separated over `Y`.

## Main definitions

- `AlgebraicGeometry.Compactification.Refinement`: the type of refinements of a
  compactification `d` by a compactification `c`;
- `AlgebraicGeometry.Compactification.Refinement.id` and
  `AlgebraicGeometry.Compactification.Refinement.comp`: the identity refinement and the
  composition of refinements;
- `AlgebraicGeometry.Compactification.category`: the category structure on the
  compactifications of `f` whose morphisms are the refinements, so that `c ⟶ d` is
  notation for `c.Refinement d`.

## Main results

- `AlgebraicGeometry.Compactification.Refinement.isProper`: the ambient morphism of a
  refinement is proper. This is an instance.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Compactification

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- A refinement of the compactification `d` by the compactification `c`: a morphism of the
ambient schemes commuting with both the open immersions and the structure morphisms. -/
@[ext]
structure Refinement (c d : Compactification f) where
  /-- The morphism of ambient schemes underlying the refinement. -/
  hom : c.Z ⟶ d.Z
  /-- The refinement commutes with the open immersions of `X`. -/
  i_hom : c.i ≫ hom = d.i
  /-- The refinement is a morphism over `Y`. -/
  hom_g : hom ≫ d.g = c.g

namespace Refinement

variable {c d e : Compactification f}

/-- The ambient morphism of a refinement is proper: it is a morphism over `Y` from a scheme
proper over `Y` to a scheme separated over `Y`. -/
instance isProper (r : Refinement c d) : IsProper r.hom :=
  have : IsProper (r.hom ≫ d.g) := by rw [r.hom_g]; exact c.isProper
  .of_comp r.hom d.g

example (r : Refinement c d) : IsProper r.hom := inferInstance

/-- The identity morphism of the ambient scheme is a refinement of a compactification by
itself. -/
@[simps]
def id (c : Compactification f) : Refinement c c where
  hom := 𝟙 c.Z
  i_hom := Category.comp_id _
  hom_g := Category.id_comp _

/-- Refinements compose: if `c` refines `d` and `d` refines `e`, then `c` refines `e`. -/
@[simps]
def comp (r : Refinement c d) (s : Refinement d e) : Refinement c e where
  hom := r.hom ≫ s.hom
  i_hom := by rw [← Category.assoc, r.i_hom, s.i_hom]
  hom_g := by rw [Category.assoc, s.hom_g, r.hom_g]

@[simp]
theorem id_comp (r : Refinement c d) : (id c).comp r = r := by ext; simp

@[simp]
theorem comp_id (r : Refinement c d) : r.comp (id d) = r := by ext; simp

theorem comp_assoc {c' : Compactification f} (r : Refinement c d) (s : Refinement d e)
    (t : Refinement e c') : (r.comp s).comp t = r.comp (s.comp t) := by ext; simp

end Refinement

/-- Blueprint `definition-compactification-refinement`: Compactifications and refinements, the
category `Comp(f)`; also part of `proposition-dense-compactifications-form-cofiltered-category`.

The compactifications of `f : X ⟶ Y` form a category, with the refinements as
morphisms: a morphism `r : c ⟶ d` is a morphism `r.hom : c.Z ⟶ d.Z` making both triangles
below commute.

```text
              X
          ╱       ╲
     c.i ╱         ╲ d.i
        ↙           ↘
      c.Z ──r.hom──→ d.Z
        ╲           ╱
     c.g ╲         ╱ d.g
          ↘       ↙
              Y
```
-/
instance category : Category.{u} (Compactification f) where
  Hom c d := c.Refinement d
  id c := Refinement.id c
  comp r s := r.comp s
  id_comp := Refinement.id_comp
  comp_id := Refinement.comp_id
  assoc := Refinement.comp_assoc

@[simp]
theorem id_hom (c : Compactification f) : Refinement.hom (𝟙 c) = 𝟙 c.Z := rfl

@[simp]
theorem comp_hom {c d e : Compactification f} (r : c ⟶ d) (s : d ⟶ e) :
    Refinement.hom (r ≫ s) = r.hom ≫ s.hom := rfl

end AlgebraicGeometry.Compactification
