/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.UnramifiedEtaleLocalDecomposition
import WeilConjectures.AlgebraicGeometry.FiniteUnramifiedEtaleLocalReduction

/-!
# Étale-local decomposition of finite unramified morphisms

Source: Stacks Project, Étale Morphisms, Lemma 04HJ
(blueprint: lem-weil-pbc-finite-unramified-etale-local).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Stacks Project, Étale Morphisms, Lemma 04HJ
(blueprint: lem-weil-pbc-finite-unramified-etale-local).
A finite unramified morphism `f : Y ⟶ X` (finite, locally of finite type, open-immersion
diagonal: def-weil-unramified-morphism) becomes a finite disjoint union of closed immersions
after passing to an étale neighbourhood of any point of its target: there are an étale
`g : U ⟶ X`, a point `u` over `x`, a finite `J` and open-and-closed pieces
`ι j : V j ⟶ Y ×_X U` exhibiting `Y ×_X U` as their coproduct (`IsColimit (Cofan.mk _ ι)`,
the spelling of the sibling lem-weil-pbc-finite-etale-etale-local-split; the pieces are then
pairwise disjoint and cover), each `ι j ≫ pullback.snd f g` a closed immersion. The
neighbourhood need not induce an isomorphism on residue fields.

Proof:
1. The fibre over `x` is finite and `f` is separated
   (`lem-weil-pbc-finite-closed-map-finite-fibres`). Enumerate its points, including the
   possibility that there are none; `f` is unramified at every one of them.
2. Apply `lem-weil-pbc-unramified-etale-local-decomposition` to those points. It gives an
   étale neighbourhood `(U, u)` and a disjoint open-and-closed decomposition of the pullback
   into finitely many pieces mapping by closed immersions to `U`, and a remainder `W` whose
   image does not contain `u`.
3. The second projection is finite by `lem-weil-pbc-finite-morphism-permanence`, hence a
   closed map by `lem-weil-pbc-finite-closed-map-finite-fibres`. Thus its image of the closed
   remainder `W` is closed and misses `u`.
4. Remove that image from `U`. The new neighbourhood is still étale by
   `def-weil-open-immersion` and `definition-torsion-sheaves--3`. Identify its
   pullback with the corresponding open of the old pullback using
   `lem-weil-pbc-open-fibre-product` and the universal property `def-pc-fibre-product`.
5. Intersect the finitely many pieces with this open. They remain open and closed, disjoint,
   and cover because the remainder has disappeared, so the new pullback is their coproduct.
   Their maps to the new neighbourhood are base changes of the old closed immersions
   (`lem-weil-pbc-open-fibre-product`), hence
   closed immersions by `lem-weil-pbc-closed-immersion-base-change`. An empty fibre allows
   the empty family. -/
theorem exists_etale_closed_immersion_decomposition_of_finite_unramified
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [LocallyOfFiniteType f]
    [IsOpenImmersion (pullback.diagonal f)] (x : X) :
    ∃ (U : Scheme.{u}) (g : U ⟶ X) (u : U),
      Etale g ∧ g.base u = x ∧
      ∃ (J : Type u) (V : J → Scheme.{u}) (ι : ∀ j, V j ⟶ pullback f g),
        Finite J ∧
        Nonempty (IsColimit (Cofan.mk (pullback f g) ι)) ∧
        (∀ j, IsOpenImmersion (ι j) ∧ IsClosedImmersion (ι j)) ∧
        (∀ j, IsClosedImmersion (ι j ≫ pullback.snd f g)) := by
  obtain ⟨n, pts, hpts, h⟩ := finite_decomposition_input f x
  exact finite_coproduct_of_unramified_decomposition f x n pts hpts h

end AlgebraicGeometry
