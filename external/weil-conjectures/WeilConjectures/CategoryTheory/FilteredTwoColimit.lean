/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Iso

/-!

# Filtered 2-colimits of categories, through their universal property on objects and morphisms

Let `I` be a directed preorder and `C i` (`i : I`) categories with transition functors
`T h : C i ⥤ C j` for `i ≤ j`. A *cocone of categories* on this system with vertex `D`
(`CategoryTheory.CategoryCocone`) is a family of functors `Φ i : C i ⥤ D` together with
isomorphisms `T h ⋙ Φ j ≅ Φ i`. No coherence between the transition functors is recorded: it is
not needed to *state* the universal property below.

The *filtered 2-colimit* `2-colim_i C i` is the ordinary category whose objects are the pairs
`(i, x)` with `x : C i` and whose morphisms `(i, x) ⟶ (j, y)` are the elements of the filtered
colimit of sets `colim_{k ≥ i, j} Hom_{C k}(T x, T y)`, composition being defined after
enlarging to a common index; a cocone induces a comparison functor `2-colim_i C i ⥤ D`,
`(i, x) ↦ (Φ i).obj x`. This comparison functor is an equivalence of ordinary categories if and
only if the cocone satisfies the following three properties, which this file records, for a
cocone `c`:

* **(Obj)** `c.EssSurjObj`: every object of `D` is isomorphic to some `(Φ i).obj x`
  (essential surjectivity);
* **(Hom)** `c.HomSurj`: every morphism `(Φ i).obj x ⟶ (Φ j).obj y` in `D` is, up to the
  structure isomorphisms, the image under some `Φ k` of a morphism `T x ⟶ T y` in `C k` for
  some `k ≥ i, j` (every morphism is defined at a finite stage);
* **(Hom)** `c.HomInj`: two morphisms of `C k` with the same image in `D` become equal in some
  `C k'`, `k ≤ k'` (equalities hold at a finite stage).

The two (Hom) properties together say that the canonical map of sets
`colim_{k} Hom_{C k}(T x, T y) ⟶ Hom_D((Φ i).obj x, (Φ j).obj y)` is a bijection, the colimit
being filtered: surjectivity is `c.HomSurj`, and injectivity reduces, after moving two
representatives to a common index, to `c.HomInj`. The conjunction of the three properties is
`c.IsFilteredTwoColimit`; it says that `D`, with the functors `Φ i`, *is* the filtered
2-colimit of the `C i`, and it uses no higher categories.

This is the formulation in which the identification of the bounded constructible
`ℚ̄_ℓ`-complexes with the 2-colimit of the bounded constructible `E`-complexes over the finite
subextensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` is stated, in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.Colimit.TwoColimit`.

-/

@[expose] public section

universe w v u v' u'

namespace CategoryTheory

variable {I : Type w} [Preorder I] (C : I → Type u) [∀ i, Category.{v} (C i)]
  (D : Type u') [Category.{v'} D]

/-- A cocone of categories on a directed system `C i` of categories indexed by a preorder,
with vertex `D`: transition functors `T h : C i ⥤ C j` for `i ≤ j`, functors `Φ i : C i ⥤ D`,
and isomorphisms `T h ⋙ Φ j ≅ Φ i`. -/
structure CategoryCocone where
  /-- The transition functors of the directed system. -/
  T : ∀ {i j : I}, i ≤ j → (C i ⥤ C j)
  /-- The functors to the vertex. -/
  Φ : ∀ i, C i ⥤ D
  /-- The compatibility of the functors to the vertex with the transition functors. -/
  iso : ∀ {i j : I} (h : i ≤ j), T h ⋙ Φ j ≅ Φ i

namespace CategoryCocone

variable {C D} (c : CategoryCocone C D)

/-- **(Obj)**: every object of the vertex is isomorphic to the image of an object at some finite
stage. This is the essential surjectivity of the comparison functor from the 2-colimit. -/
def EssSurjObj : Prop :=
  ∀ d : D, ∃ (i : I) (x : C i), Nonempty ((c.Φ i).obj x ≅ d)

/-- **(Hom), surjectivity**: every morphism `(Φ i).obj x ⟶ (Φ j).obj y` of the vertex is, up to
the structure isomorphisms, the image under `Φ k` of a morphism `T x ⟶ T y` at some finite
stage `k ≥ i, j`. -/
def HomSurj : Prop :=
  ∀ (i j : I) (x : C i) (y : C j) (f : (c.Φ i).obj x ⟶ (c.Φ j).obj y),
    ∃ (k : I) (hi : i ≤ k) (hj : j ≤ k) (g : (c.T hi).obj x ⟶ (c.T hj).obj y),
      f = (c.iso hi).inv.app x ≫ (c.Φ k).map g ≫ (c.iso hj).hom.app y

/-- **(Hom), injectivity**: two morphisms at a finite stage `k` with the same image in the
vertex become equal at some finite stage `k' ≥ k`. -/
def HomInj : Prop :=
  ∀ (k : I) (x y : C k) (g g' : x ⟶ y), (c.Φ k).map g = (c.Φ k).map g' →
    ∃ (k' : I) (h : k ≤ k'), (c.T h).map g = (c.T h).map g'

/-- A cocone of categories *is a filtered 2-colimit* if it satisfies (Obj) and the two halves
of (Hom): the comparison functor from the 2-colimit of the `C i` to the vertex is then an
equivalence of ordinary categories. -/
structure IsFilteredTwoColimit : Prop where
  essSurjObj : c.EssSurjObj
  homSurj : c.HomSurj
  homInj : c.HomInj

/-- If a cocone of categories is a filtered 2-colimit, every object of the vertex is
isomorphic to one coming from a finite stage. -/
lemma IsFilteredTwoColimit.exists_iso (hc : c.IsFilteredTwoColimit) (d : D) :
    ∃ (i : I) (x : C i), Nonempty ((c.Φ i).obj x ≅ d) :=
  hc.essSurjObj d

/-- In a filtered 2-colimit, the functors `Φ k` are jointly faithful up to enlarging the
index: this is the (Hom) injectivity property restated. -/
lemma IsFilteredTwoColimit.exists_map_eq (hc : c.IsFilteredTwoColimit) {k : I} {x y : C k}
    {g g' : x ⟶ y} (h : (c.Φ k).map g = (c.Φ k).map g') :
    ∃ (k' : I) (h : k ≤ k'), (c.T h).map g = (c.T h).map g' :=
  hc.homInj k x y g g' h

end CategoryCocone

end CategoryTheory
