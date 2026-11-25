/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Galois.Equivalence

/-!
# The topology on `Aut F` and the abstract equivalence theorem

Let `F : C ⥤ FintypeCat` be a functor. The group `Aut F` carries the topology induced by the
evaluation embedding `Aut F ⟶ ∏_X Aut (F X)`, the target carrying the product of the discrete
topologies. This file restates, in the form of the blueprint, the following results of
Mathlib's Galois theory:

- the action of `Aut F` on each fibre is continuous (blueprint `lem-galois-action-continuous`);
- the evaluation embedding is a closed embedding, so `Aut F` is profinite (blueprint
  `lem-galois-aut-profinite`);
- every connected object of a Galois category is dominated by a Galois object (blueprint
  `lem-galois-object-exists`);
- `Aut F` acts transitively on the fibre of a connected object (blueprint
  `lem-galois-transitive`);
- `F` induces an equivalence with finite discrete `Aut F`-sets (blueprint
  `thm-galois-abstract-equivalence`).
-/

@[expose] public section

universe u₁ u₂ w

open CategoryTheory Limits Functor

namespace CategoryTheory.PreGaloisCategory

section Topology

variable {C : Type u₁} [Category.{u₂} C] (F : C ⥤ FintypeCat.{w})

/-- **Continuity of the action of `Aut F`.** For every functor `F` to finite sets and every
object `X`, the action map `Aut F × F(X) → F(X)` is continuous for the discrete topology on
`F(X)`. (blueprint: `lem-galois-action-continuous`) -/
theorem continuous_smul_aut_fiber (X : C) :
    Continuous (fun p : Aut F × F.obj X ↦ p.1 • p.2) :=
  (continuousSMul_aut_fiber F X).continuous_smul

/-- **`Aut F` is profinite.** The evaluation embedding identifies `Aut F` with a closed subgroup of
`∏_X Aut (F X)`, and consequently `Aut F` is a compact, Hausdorff and totally disconnected
topological group. (blueprint: `lem-galois-aut-profinite`) -/
theorem isClosedEmbedding_autEmbedding_and_profinite :
    Topology.IsClosedEmbedding (autEmbedding F) ∧ CompactSpace (Aut F) ∧ T2Space (Aut F) ∧
      TotallyDisconnectedSpace (Aut F) ∧ IsTopologicalGroup (Aut F) :=
  ⟨autEmbedding_isClosedEmbedding F, inferInstance, inferInstance, inferInstance, inferInstance⟩

end Topology

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C] (F : C ⥤ FintypeCat.{w})
  [FiberFunctor F]

include F in
/-- **Galois objects dominate connected objects.** For every connected object `X` there are a
Galois object `Z` and a morphism `Z ⟶ X`. (blueprint: `lem-galois-object-exists`) -/
theorem exists_isGalois_hom (X : C) [IsConnected X] : ∃ (Z : C) (_ : Z ⟶ X), IsGalois Z := by
  obtain ⟨Z, f, h⟩ := exists_hom_from_galois_of_connected F X
  exact ⟨Z, f, h⟩

/-- **The action of `Aut F` is transitive** on the fibre of every connected object.
(blueprint: `lem-galois-transitive`) -/
theorem isPretransitive_aut_fiber (X : C) [IsConnected X] :
    MulAction.IsPretransitive (Aut F) (F.obj X) :=
  inferInstance

open scoped FintypeCatDiscrete in
/-- **The abstract equivalence theorem.** The functor from `C` to finite discrete
`Aut F`-sets, `X ↦ F(X)` with the induced action, is an equivalence of categories.
(blueprint: `thm-galois-abstract-equivalence`) -/
theorem isEquivalence_functorToContAction : (functorToContAction F).IsEquivalence :=
  inferInstance

end CategoryTheory.PreGaloisCategory
