/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Category.Preorder
import WeilConjectures.Algebra.FiniteFamilyCommonStage
import WeilConjectures.Algebra.Homology.PreorderModuleMapEqualityDescent

/-! # Simultaneous eventual equality of finitely many module maps

Source: Stacks Project, Algebra, Tag 05N7, clause (3).
(blueprint: lem-pc-finite-family-module-map-equality-colimit).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- A finite family of equalities of maps over the colimit holds at one later stage.

Source: Stacks Project, Algebra, Tag 05N7, clause (3), used in More on Algebra,
Tag 0BC7, proof of (1).
(blueprint: lem-pc-finite-family-module-map-equality-colimit).

Proof: For each t, apply the equality clause of finite-presentation descent to f t and
 g t and choose a stage above i where they agree. Directedness supplies a common upper
bound for these finitely many stages and i. Map each equality to that upper stage;
functoriality of extension of scalars and its canonical composition isomorphism
identify the result with the asserted equality. For an empty family use i itself.
For a preorder, replace I by its antisymmetrization, choose representatives, and transport
F and its colimit along the equivalence of indexing categories. Apply the partial-order
statement there and lift the resulting upper index back to I; the definition of the
quotient order guarantees that it is above i. The canonical ring and module comparison
isomorphisms preserve and reflect the equalities of maps in question. -/
theorem exists_stage_finite_family_map_eq
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F]
    (i : I) {T : Type v} [Finite T]
    (M N : T → ModuleCat.{u} (F.obj i))
    (hM : ∀ t, Module.FinitePresentation (F.obj i) (M t))
    (hN : ∀ t, Module.FinitePresentation (F.obj i) (N t))
    (f g : ∀ t, M t ⟶ N t)
    (h : ∀ t, (extendScalars (colimit.ι F i).hom).map (f t) =
      (extendScalars (colimit.ι F i).hom).map (g t)) :
    ∃ (j : I) (hij : i ≤ j), ∀ t,
      (extendScalars (F.map (homOfLE hij)).hom).map (f t) =
        (extendScalars (F.map (homOfLE hij)).hom).map (g t) := by
  classical
  have hs : ∀ t, ∃ j : I, ∃ hij : i ≤ j,
      (extendScalars (F.map (homOfLE hij)).hom).map (f t) =
        (extendScalars (F.map (homOfLE hij)).hom).map (g t) := by
    intro t
    exact eventually_equal_maps_of_directed_preorder_colimit F i (M t) (N t)
      (hM t) (hN t) (f t) (g t) (h t)
  exact exists_common_stage_of_stage_equalities F i M N f g hs

end ModuleCat
