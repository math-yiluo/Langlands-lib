/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.Compactification.Constructions
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Compactification of a composite

Let `f : X ⟶ Y` and `g : Y ⟶ S`. A compactification `d = (Y ⟶[d.i] d.Z ⟶[d.g] S)` of `g` and a
compactification `e` of `f ≫ d.i` give the compactification `X ⟶[e.i] e.Z ⟶[e.g ≫ d.g] S` of
`f ≫ g`. This is `Compactification.postcomp` for the proper morphism `d.g`; the compactification
`e` of `f ≫ d.i` is an input, which in general comes from Nagata's compactification theorem.

Conversely, a compactification `e` of `f ≫ m` for a monomorphism `m : Y ⟶ W` restricts to a
compactification of `f`: since `m` is a monomorphism, the square
`IsPullback (𝟙 X) f (f ≫ m) m` is cartesian, and base changing `e` along it gives the
compactification `X ⟶ e.Z ×_W Y ⟶ Y` of `f`. For `m = d.i` this is the compactification of `f`
used in the proof of the composition law `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`, which rests on the
cartesian squares
```
  X -------𝟙 X------> X           e.Z ×_W Y ---fst---> e.Z
  |                   |           |                     |
  e.restrict.i       e.i          e.restrict.g         e.g
  ↓                   ↓           ↓                     ↓
  e.Z ×_W Y --fst--> e.Z          Y --------m--------> W
```

## Main definitions

- `AlgebraicGeometry.Compactification.comp`: the compactification `(e.i, e.g ≫ d.g)` of
  `f ≫ g`.
- `AlgebraicGeometry.Compactification.restrict`: the compactification of `f` with compactifying
  scheme `e.Z ×_W Y`, for `e` a compactification of `f ≫ m` and `m` a monomorphism.

## Main results

- `AlgebraicGeometry.Compactification.isPullback_i_restrict` and
  `AlgebraicGeometry.Compactification.isPullback_restrict`: the two cartesian squares above.

## Blueprint

The constructions of this file are ingredients of the successive compactifications used in
`thm:ambient-shriek-composition`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Compactification

section Comp

variable {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S}

/-- **Compactifying a composite through a compactification of the second map**: if `d`
compactifies `g : Y ⟶ S` and `e` compactifies `f ≫ d.i`, then `X ⟶[e.i] e.Z ⟶[e.g ≫ d.g] S`
compactifies `f ≫ g`. This is `Compactification.postcomp e d.g`, transported along
`f ≫ g = (f ≫ d.i) ≫ d.g`; it does not produce a compactification of `f ≫ g` from
compactifications of `f` and `g` alone.

Note that `d` must come first since the type of `e` depends on `d.i`.
```
  X --e.i--> e.Z
  |           |
  f          e.g
  ↓           ↓
  Y --d.i--> d.Z
    \         |
     g       d.g
      \       ↓
       -----> S
```
-/
@[simps! Z g i]
noncomputable def comp (d : Compactification g) (e : Compactification (f ≫ d.i)) :
    Compactification (f ≫ g) :=
  (e.postcomp d.g).copy (by rw [Category.assoc, ← d.comm])

end Comp

section Restrict

variable {X Y W : Scheme.{u}} {f : X ⟶ Y} {m : Y ⟶ W} [Mono m] (e : Compactification (f ≫ m))

/-- **Restricting a compactification to a subobject**: for a monomorphism `m : Y ⟶ W` and a
compactification `e` of `f ≫ m`, the compactification of `f` with compactifying scheme
`e.Z ×_W Y`, obtained by base changing `e` along the cartesian square
`IsPullback.id_comp_of_mono f m`. -/
@[simps! Z g]
noncomputable def restrict : Compactification f :=
  e.ofIsPullback (.id_comp_of_mono f m)

/-- The open immersion of `e.restrict` followed by the projection to `e.Z` is `e.i`. -/
@[reassoc (attr := simp)] lemma restrict_i_fst : e.restrict.i ≫ pullback.fst e.g m = e.i :=
  (ofIsPullback_i_fst _ e).trans (Category.id_comp _)

/-- The open immersion of `e.restrict` is the base change of `e.i` along the projection:
```
  X -------𝟙 X------> X
  |                   |
  e.restrict.i       e.i
  ↓                   ↓
  e.Z ×_W Y --fst--> e.Z
```
-/
theorem isPullback_i_restrict : IsPullback (𝟙 X) e.restrict.i e.i (pullback.fst e.g m) :=
  e.isPullback_i_ofIsPullback _

/-- The proper morphism of `e.restrict` is the base change of `e.g` along `m`:
```
  e.Z ×_W Y ---fst---> e.Z
  |                     |
  e.restrict.g         e.g
  ↓                     ↓
  Y --------m--------> W
```
-/
theorem isPullback_restrict : IsPullback e.restrict.g (pullback.fst e.g m) m e.g :=
  e.isPullback_g_ofIsPullback _

end Restrict

section OfComp

variable {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S}

/-- The immersion `X ⟶ c.Z ×_S d.Z` with components `c.i` and `f ≫ d.i`, for a
compactification `c` of `f ≫ g` and a compactification `d` of `g`. -/
noncomputable def ofCompLift (c : Compactification (f ≫ g)) (d : Compactification g) :
    X ⟶ pullback c.g d.g :=
  pullback.lift c.i (f ≫ d.i) (by rw [← c.comm, Category.assoc, ← d.comm])

@[reassoc (attr := simp)]
lemma ofCompLift_fst (c : Compactification (f ≫ g)) (d : Compactification g) :
    c.ofCompLift d ≫ pullback.fst c.g d.g = c.i :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma ofCompLift_snd (c : Compactification (f ≫ g)) (d : Compactification g) :
    c.ofCompLift d ≫ pullback.snd c.g d.g = f ≫ d.i :=
  pullback.lift_snd _ _ _

instance (c : Compactification (f ≫ g)) (d : Compactification g) :
    IsImmersion (c.ofCompLift d) :=
  have : IsImmersion (c.ofCompLift d ≫ pullback.fst c.g d.g) := by
    rw [ofCompLift_fst]; infer_instance
  .of_comp _ (pullback.fst c.g d.g)

/-- **Compactifying `f` into a compactification of `g`**: for a quasi-compact composite
`f ≫ g`, a compactification `c` of `f ≫ g` and a compactification `d` of `g`, the closure of
`X` in `c.Z ×_S d.Z` (embedded by `c.i` and `f ≫ d.i`) is a compactification of `f ≫ d.i`.
Together with `Compactification.comp` and `Compactification.restrict` this produces, out of
compactifications of `g` and of `f ≫ g`, the compactifications of `f` and `f ≫ g` used in the
composition law `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` (blueprint
`proposition-composition-base-change-rf-shriek--1`). -/
noncomputable def ofComp [QuasiCompact (f ≫ g)] (c : Compactification (f ≫ g))
    (d : Compactification g) : Compactification (f ≫ d.i) :=
  have : QuasiCompact (c.ofCompLift d) :=
    have : QuasiCompact (c.ofCompLift d ≫ pullback.fst c.g d.g) := by
      rw [ofCompLift_fst]; exact c.quasiCompact_openImmersion inferInstance
    .of_comp _ (pullback.fst c.g d.g)
  (ofIsImmersion (c.ofCompLift d) (pullback.snd c.g d.g)).copy (ofCompLift_snd c d).symm

end OfComp

end Compactification

end AlgebraicGeometry
