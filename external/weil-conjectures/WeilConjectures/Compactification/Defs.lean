/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!

# Compactifications of morphisms of schemes

A compactification of a morphism of schemes `f : X ⟶ Y` is a factorization `f = i ≫ g`
where `g : Z ⟶ Y` is proper and `i : X ⟶ Z` is an open immersion. We record
the data of a compactification of `f` in the class
`AlgebraicGeometry.Compactification f`.

We derive the properties of the morphisms involved in a compactification:

- `Compactification.isSeparated`: `f` is separated;
- `Compactification.locallyOfFiniteType`: `f` is locally of finite type;
- `Compactification.quasiCompact_openImmersion_iff`: `i` is quasi-compact if and only
  if `f` is;
- `Compactification.isProper_openImmersion`, `Compactification.isClosedImmersion_openImmersion`
  and `Compactification.isClopen_range_openImmersion`: if `f` is proper, then `i` is proper,
  hence a closed immersion with clopen range;
- `Compactification.ofIsProper`: a proper morphism is a compactification of itself;
- `Compactification.copy` and `HasCompactification.of_eq`: a compactification of `f` is one
  of any morphism equal to `f`;
- `Compactification.transport`: a compactification transports along isomorphisms of the
  source and the target;
- `Compactification.precomp` and `HasCompactification.comp_of_isOpenImmersion`:
  compactifiability is inherited by open subschemes of the source.
- `Compactification.postcomp` and `HasCompactification.comp_of_isProper`: compactifiability
  is preserved by postcomposition with a proper morphism.

Finally, we define the class `AlgebraicGeometry.HasCompactification f`, asserting
`Nonempty (Compactification f)`. Nagata's compactification theorem asserts
`HasCompactification f` whenever `f` is separated and of finite type (and `Y` is
quasi-compact and quasi-separated). Any `f` satisfying `HasCompactification f` is
separated and locally of finite type; these are instances.
A choice of compactification is extracted from `HasCompactification f` by
`HasCompactification.compactification f`.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The data of a compactification of `f : X ⟶ Y`: a scheme `Z` together with a proper
morphism `g : Z ⟶ Y` and an open immersion `i : X ⟶ Z` such that `f = i ≫ g`.

The open immersion `i` is not required to be quasi-compact, unlike in the blueprint
(`definition-compactification-refinement--1`) and in Stacks/Conrad, where `j` is a quasi-compact
open immersion. When `f` is quasi-compact, which is the case in all uses of Nagata's theorem, the
two notions agree: `i` is then automatically quasi-compact
(`AlgebraicGeometry.Compactification.quasiCompact_openImmersion_iff`). The weaker
requirement is what lets a compactification be restricted along an arbitrary open immersion
(`AlgebraicGeometry.Compactification.precomp`). -/
structure Compactification {X Y : Scheme.{u}} (f : X ⟶ Y) where
  /-- The scheme in which `X` is compactified. -/
  Z : Scheme.{u}
  /-- The structure morphism of the compactification, which is proper. -/
  g : Z ⟶ Y
  /-- The open immersion of `X` into the compactification. -/
  i : X ⟶ Z
  /-- `f` factors as the open immersion `i` followed by the structure morphism `g`. -/
  comm : f = i ≫ g
  /-- The structure morphism `g` is proper. -/
  isProper : IsProper g
  /-- The morphism `i` is an open immersion. -/
  isOpenImmersion : IsOpenImmersion i

attribute [instance] Compactification.isProper Compactification.isOpenImmersion

namespace Compactification

variable {X Y : Scheme.{u}}

/-- A proper morphism is a compactification of itself. -/
def ofIsProper (f : X ⟶ Y) [IsProper f] : Compactification f where
  Z := X
  g := f
  i := 𝟙 X
  comm := (Category.id_comp f).symm
  isProper := inferInstance
  isOpenImmersion := inferInstance

/-- An open immersion is compactified by the identity of its target. -/
def ofIsOpenImmersion (f : X ⟶ Y) [IsOpenImmersion f] : Compactification f where
  Z := Y
  g := 𝟙 Y
  i := f
  comm := (Category.comp_id f).symm
  isProper := inferInstance
  isOpenImmersion := inferInstance

variable {f : X ⟶ Y}

/-- Transport a compactification along an equality of morphisms: if `f' = f`, then a
compactification of `f` is one of `f'`, with the same data. -/
@[simps]
def copy (c : Compactification f) {f' : X ⟶ Y} (h : f' = f) : Compactification f' where
  Z := c.Z
  g := c.g
  i := c.i
  comm := h.trans c.comm
  isProper := c.isProper
  isOpenImmersion := c.isOpenImmersion

/-- The compactification of `f'` transported from a compactification `X ⟶[i] Z ⟶[g] Y` of `f`
along isomorphisms `eX : X ≅ X'`, `eY : Y ≅ Y'` with `f ≫ eY = eX ≫ f'`;
its open immersion and its proper morphism are the composites
```
X' --eX⁻¹--> X --i--> Z --g--> Y --eY--> Y'
```
-/
@[simps]
def transport {X' Y' : Scheme.{u}} {f' : X' ⟶ Y'} (eX : X ≅ X') (eY : Y ≅ Y')
    (w : f ≫ eY.hom = eX.hom ≫ f') (c : Compactification f) : Compactification f' where
  Z := c.Z
  g := c.g ≫ eY.hom
  i := eX.inv ≫ c.i
  comm := by
    rw [Category.assoc, ← Category.assoc c.i, ← c.comm, w, Iso.inv_hom_id_assoc]
  isProper := inferInstance
  isOpenImmersion := inferInstance

/-- **Compactifications restrict to open subschemes**: if `c` is a compactification of
`f : X ⟶ Y` and `e : X' ⟶ X` is an open immersion, then composing `e` with the open
immersion of `c` exhibits a compactification of `e ≫ f`, with the same ambient scheme. -/
@[simps]
def precomp {X' : Scheme.{u}} (c : Compactification f) (e : X' ⟶ X) [IsOpenImmersion e] :
    Compactification (e ≫ f) where
  Z := c.Z
  g := c.g
  i := e ≫ c.i
  comm := by rw [Category.assoc, ← c.comm]
  isProper := c.isProper
  isOpenImmersion := inferInstance

/-- **Postcomposing a compactification with a proper morphism**: if `c` is a compactification
of `f : X ⟶ Y` and `p : Y ⟶ S` is proper, then composing `c.g` with `p` exhibits a
compactification of `f ≫ p`, with the same ambient scheme.
```
  X --c.i--> c.Z
    \         |
   f ≫ p    c.g ≫ p
      \       ↓
       -----> S
```
-/
@[simps]
def postcomp {S : Scheme.{u}} (c : Compactification f) (p : Y ⟶ S) [IsProper p] :
    Compactification (f ≫ p) where
  Z := c.Z
  g := c.g ≫ p
  i := c.i
  comm := by rw [← Category.assoc, ← c.comm]
  isProper := inferInstance
  isOpenImmersion := inferInstance

variable (c : Compactification f)
include c

/-- A morphism admitting a compactification is separated. -/
theorem isSeparated : IsSeparated f := by
  rw [c.comm]
  infer_instance

/-- A morphism admitting a compactification is locally of finite type. -/
theorem locallyOfFiniteType : LocallyOfFiniteType f := by
  rw [c.comm]
  infer_instance

/-- If the open immersion into a compactification is quasi-compact, the compactified
morphism is quasi-compact. -/
theorem quasiCompact (hi : QuasiCompact c.i) : QuasiCompact f := by
  rw [c.comm]
  infer_instance

/-- The open immersion into a compactification of a quasi-compact morphism is
quasi-compact. -/
theorem quasiCompact_openImmersion (hf : QuasiCompact f) : QuasiCompact c.i := by
  have : QuasiCompact (c.i ≫ c.g) := c.comm ▸ hf
  exact .of_comp c.i c.g

/-- The open immersion into a compactification is quasi-compact if and only if the
compactified morphism is. -/
theorem quasiCompact_openImmersion_iff : QuasiCompact c.i ↔ QuasiCompact f :=
  ⟨c.quasiCompact, c.quasiCompact_openImmersion⟩

/-- The open immersion into a compactification of a **proper** morphism is itself proper:
`c.i` is proper as soon as `c.i ≫ c.g` is, because `c.g` is separated. -/
theorem isProper_openImmersion (hf : IsProper f) : IsProper c.i :=
  have : IsProper (c.i ≫ c.g) := c.comm ▸ hf
  .of_comp c.i c.g

/-- The open immersion into a compactification of a proper morphism is also a **closed**
immersion. -/
theorem isClosedImmersion_openImmersion (hf : IsProper f) : IsClosedImmersion c.i :=
  have := c.isProper_openImmersion hf
  .of_isOpenImmersion_of_universallyClosed c.i

/-- The open immersion into a compactification of a proper morphism identifies `X` with a
**clopen** subscheme of the compactification: its range is open, being an open immersion,
and closed, being universally closed. -/
theorem isClopen_range_openImmersion (hf : IsProper f) : IsClopen (Set.range c.i) :=
  have := c.isProper_openImmersion hf
  Scheme.Hom.isClopen_range c.i

end Compactification

variable {X Y : Scheme.{u}}

/-- A morphism `f : X ⟶ Y` has a compactification if it factors as an open
immersion followed by a proper morphism, i.e. `f` is *compactifiable*, such a factorization
being a `Compactification f`. This is blueprint `definition-compactification-refinement--1`. -/
class HasCompactification (f : X ⟶ Y) : Prop where
  /-- Some compactification of `f` exists. -/
  nonempty_compactification : Nonempty (Compactification f)

attribute [instance low] HasCompactification.nonempty_compactification

lemma Compactification.hasCompactification {f : X ⟶ Y} (c : Compactification f) :
    HasCompactification f := ⟨⟨c⟩⟩

/-- A choice of compactification of `f`, extracted from a `HasCompactification f`
instance using choice. -/
@[no_expose]
noncomputable def HasCompactification.compactification (f : X ⟶ Y) [hf : HasCompactification f] :
    AlgebraicGeometry.Compactification f :=
  Classical.arbitrary _

namespace HasCompactification

/-- A proper morphism has a compactification, namely itself. -/
instance (priority := 100) of_isProper (f : X ⟶ Y) [IsProper f] : HasCompactification f :=
  ⟨⟨.ofIsProper f⟩⟩

/-- Compactifiability transports along an equality of morphisms. -/
lemma of_eq {f g : X ⟶ Y} [HasCompactification f] (h : f = g) : HasCompactification g :=
  h ▸ ‹_›

variable (f : X ⟶ Y) [hf : HasCompactification f]

/-- A morphism admitting a compactification is separated. -/
instance isSeparated : IsSeparated f := hf.compactification.isSeparated

/-- A morphism admitting a compactification is locally of finite type. -/
instance locallyOfFiniteType : LocallyOfFiniteType f := hf.compactification.locallyOfFiniteType

/-- **Compactifiability is inherited by open subschemes**: if `f : X ⟶ Y` admits a
compactification, then so does its restriction `e ≫ f` along any open immersion
`e : X' ⟶ X`. -/
theorem comp_of_isOpenImmersion {X' : Scheme.{u}} (e : X' ⟶ X) [IsOpenImmersion e] :
    HasCompactification (e ≫ f) :=
  ((compactification f).precomp e).hasCompactification

/-- **Compactifiability is preserved by proper postcomposition**: if `f : X ⟶ Y` admits a
compactification and `p : Y ⟶ S` is proper, then `f ≫ p` admits one too. -/
theorem comp_of_isProper {S : Scheme.{u}} (p : Y ⟶ S) [IsProper p] :
    HasCompactification (f ≫ p) :=
  ((compactification f).postcomp p).hasCompactification

end HasCompactification

end AlgebraicGeometry
