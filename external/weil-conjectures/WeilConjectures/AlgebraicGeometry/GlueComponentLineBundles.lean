/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.ExistsGluedInvertible
import WeilConjectures.AlgebraicGeometry.ExistsGluedSection

/-!
# Gluing invertible modules and sections across components

Source: literature/stacks-project/varieties.tex, Varieties Lemma 09NE
(varieties-lemma-glue-invertible-sheaves) (blueprint: lem-sc-glue-component-line-bundles).
-/

@[expose] public section

universe u v

open CategoryTheory Opposite AlgebraicGeometry
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/--
Let `Y` be reduced and covered by finitely many closed subschemes `i a : Z a ⟶ Y` with
discrete pairwise intersections. Invertible modules `M a` on the components glue to an
invertible module on `Y`, and sections nonvanishing at every point of the pairwise
intersections glue as well (Stacks, Varieties Lemma 09NE).
Module pullback is `tensorPullback` (def-pc-module-pullback); `res N a` is restriction of
global sections to `Z a`, the unit of its canonical adjunction
(lem-pc-module-pullback-adjunction). `X_s` is `nonvanishingLocus`
(def-weil-pbc-ample-invertible-module): nonzero in the residue-field fibre.

Proof (the direct proof of Varieties Lemma 09NE):
1. Let `T` be the union of pairwise intersections. It is closed and discrete. Off `T`,
   the components form a disjoint scheme cover, by reducedness. The restriction identity
   for sections is `lem-sc-glue-component-reduced-cover-sections`.
2. Choose neighbourhoods `U_t` meeting `T` only at `t`. Shrink them to trivialize every
   component module, excluding components not containing `t`. In the prescribed-section
   case shrink further until each section is a generator, and choose its frame to send
   it to `1`. Cover each component off `T` by trivializing opens `U_ij` of `Y`.
3. Use the component frame changes on overlaps. Opens from different components off
   `T` are disjoint. The restriction identity in step 1 identifies component functions
   with functions on overlaps in `Y`, including the product decomposition for overlaps
   of distinct `U_t`. The frame changes satisfy the cocycle condition. Apply
   `lem-sc-glue-component-transition-cocycle` to glue the invertible module and its
   component restriction isomorphisms.
4. For prescribed sections, take `1` on each `U_t` and the local expression of `s_i`
   on each `U_ij`. The normalized frames make these expressions compatible with the
   transition cocycle of step 3 (`lem-sc-glue-component-transition-cocycle`). The sheaf
   condition glues them to one global section restricting to all the prescribed sections.
(blueprint: lem-sc-glue-component-line-bundles)
-/
theorem glueComponentLineBundles
    {Y : Scheme.{u}} [IsReduced Y] {ι : Type v} [Finite ι]
    (Z : ι → Scheme.{u}) (i : ∀ a : ι, Z a ⟶ Y) [∀ a : ι, IsClosedImmersion (i a)]
    (hcover : (⋃ a : ι, Set.range (i a)) = Set.univ)
    (hdiscrete : ∀ a b : ι, a ≠ b →
      DiscreteTopology ↥(Set.range (i a) ∩ Set.range (i b)))
    (M : ∀ a : ι, (Z a).Modules) [∀ a : ι, (M a).IsInvertible] :
    let res : ∀ (N : Y.Modules) (a : ι), Γ(N, ⊤) → Γ((tensorPullback (i a)).obj N, ⊤) :=
      fun N a t ↦
        ((Classical.choose (exists_tensorPullbackAdjunction (i a))).unit.app N).val.app
          (op ⊤) t
    (∃ N : Y.Modules, N.IsInvertible ∧
      ∀ a : ι, Nonempty ((tensorPullback (i a)).obj N ≅ M a)) ∧
    ∀ s : ∀ a : ι, Γ(M a, ⊤),
      (∀ a b : ι, a ≠ b → Set.range (i a) ∩ Set.range (i b) ⊆
        i a '' nonvanishingLocus (M a) (s a)) →
      ∃ (N : Y.Modules) (t : Γ(N, ⊤)), N.IsInvertible ∧
        ∀ a : ι, ∃ e : (tensorPullback (i a)).obj N ≅ M a,
          e.hom.val.app (op ⊤) (res N a t) = s a := by
  dsimp
  constructor
  · exact existsGluedInvertible Z i hcover hdiscrete M
  · intro s hs
    exact existsGluedSection Z i hcover hdiscrete M s hs

end AlgebraicGeometry.Scheme.Modules
