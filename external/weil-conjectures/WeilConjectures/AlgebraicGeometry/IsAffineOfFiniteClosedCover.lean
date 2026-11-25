/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.SurjectiveUniversallyClosedAffineTarget
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Affineness from a finite closed cover

Source: Stacks Project, Limits, Lemma 32.11.3 (Tag 09NL)
(blueprint: lem-sc-closed-affine-union-affine).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A scheme covered set theoretically by finitely many affine closed subschemes is affine.
Source: Stacks Project, Limits, Lemma 32.11.3 (Tag 09NL)
(blueprint: lem-sc-closed-affine-union-affine).

Proof:
1. If `r = 0`, the covering hypothesis makes `Y` empty, hence the spectrum of the zero ring
   and affine [def-weil-affine-spectrum].
2. The disjoint union `W` of the `Z j` is affine, as a finite coproduct of affine schemes
   [lem-weil-pbc-affine-morphism-permanence, clause 4].
3. Each closed immersion is finite [lem-weil-pbc-closed-immersion-finite]. Inductively,
   the induced map `W → Y` is finite by [lem-weil-pbc-finite-coproduct], hence satisfies
   [def-weil-finite-integral-morphism].
4. This map is surjective because its image is the union of the images of the `i j`
   [def-weil-surjective-morphism]. Finiteness implies universal closedness
   [lem-weil-pbc-finite-closed-map-finite-fibres, clause 1; def-weil-proper-morphism].
5. A surjective universally closed morphism with affine source has affine target
   [lem-weil-pbc-surjective-universally-closed-affine-target] (Stacks, Proposition 05YU).
-/
theorem isAffine_of_finite_closed_cover (Y : Scheme.{u}) (r : ℕ)
    (Z : Fin r → Scheme.{u}) (i : ∀ j : Fin r, Z j ⟶ Y)
    [∀ j : Fin r, IsAffine (Z j)] [∀ j : Fin r, IsClosedImmersion (i j)]
    (hcover : ∀ y : Y, ∃ j : Fin r, ∃ z : Z j, i j z = y) : IsAffine Y := by
  let f : (Limits.sigmaObj Z) ⟶ Y := Limits.Sigma.desc i
  have : IsAffine (Limits.sigmaObj Z) := inferInstance
  have : IsFinite f := inferInstance
  have : Surjective f := by
    apply Surjective.sigmaDesc_of_union_range_eq_univ
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨j, z, hz⟩ := hcover y
    exact Set.mem_iUnion.mpr ⟨j, z, hz⟩
  exact isAffine_of_surjective_of_universallyClosed f

end AlgebraicGeometry
