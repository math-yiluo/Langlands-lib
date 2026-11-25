/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.GenericFiniteSchemeSplitting
import WeilConjectures.AlgebraicGeometry.FiniteSplitCoverLisseImage
import WeilConjectures.AlgebraicGeometry.LisseEtaleSurjectiveDescent

/-!
# A generic locus where a finite map preserves lissity

Source: smooth purity blueprint, `sk-prop-sf-cbc`,
`lem-weil-pbc-finite-pushforward-generic-constructible`, finite-algebra calculation
and final paragraph.
(blueprint: lem-weil-pbc-finite-map-generic-lisse-preservation).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- There is a dense open depending only on a finite morphism, over every open of
which its direct image preserves finite local constancy. No constructibility of E
is assumed: only its restriction to the inverse image of V needs to be lisse.

Source: smooth purity blueprint, `sk-prop-sf-cbc`,
`lem-weil-pbc-finite-pushforward-generic-constructible`, finite-algebra calculation
and final paragraph.
(blueprint: lem-weil-pbc-finite-map-generic-lisse-preservation).

Proof:
1. Write S = Spec A and Z = Spec B (finite morphisms are affine). Apply
`lem-weil-pbc-generic-finite-algebra-splitting` to the finite A-algebra B. For a
nonzero c this supplies a finite surjective etale cover S' of the dense principal
open U = D(c); the reduction of Z ×_S S' is a finite disjoint union of finite
surjective universal homeomorphisms onto S'. This choice depends on g alone.
2. For any V ≤ U restrict this cover and the splitting to V. Universal
homeomorphisms and the reduction equivalence remain so after base change.
The splitting is preserved because finite disjoint unions and the algebra
product decomposition restrict to open subschemes. Reduction also commutes with
open restriction. Thus the same description holds over the cover S' ×_S V.
3. Suppose E|g⁻¹(V) is lisse. Its pullbacks to the reduced components are lisse:
pullback preserves finite local constancy
(`lem-weil-pbc-pullback-finite-locally-constant`). By
`thm-weil-pbc-universal-homeomorphism-invariance`, direct image along each
component equivalence is the inverse of pullback. It carries a lisse sheaf to a
lisse sheaf: transport its trivializing etale cover through the site equivalence;
the geometric stalks are identified under the unique lifted geometric point.
4. Sections on the finite disjoint union are the product of sections on the
components. This product is lisse: refine finitely many trivializing etale covers
by their fibre product, on which it is the constant sheaf of the finite product
of their finite stalks. If the product has no factors, the abelian direct image
is zero and its underlying set sheaf is the constant singleton sheaf.
5. Finite exchange (`lemma-weil-pbc-finite-exchange`) identifies that direct
image with the pullback of (g_*E)|V. Forgetting abelian structure commutes with
inverse image and direct image by
`situation-conventions`. Isomorphisms transport
trivializations and finiteness of geometric stalks. Compose the trivializing
etale cover with S' ×_S V → V to obtain a trivializing etale cover of V;
every geometric point lifts to this surjective cover, so its stalk is finite.
This proves lissity of the displayed restricted direct image for every V ≤ U. -/
theorem exists_dense_open_finite_lisse_preservation
    (S : Scheme.{u}) [IsIntegral S] [IsNoetherian S] [IsAffine S]
    {Z : Scheme.{u}} (g : Z ⟶ S) [IsFinite g] :
    ∃ U : S.Opens, Dense (U : Set S) ∧
      ∀ (V : S.Opens), V ≤ U →
        ∀ (E : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}),
          IsLisseEtaleSheafOfSets
            ((sheafCompose (g ⁻¹ᵁ V).toScheme.smallEtaleTopology
              (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
                ((Etale.upperStar AddCommGrpCat.{u + 1} (g ⁻¹ᵁ V).ι).obj E)) →
          IsLisseEtaleSheafOfSets
            ((etaleSetPullback V.ι).obj
              ((sheafCompose S.smallEtaleTopology
                (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
                  ((Etale.lowerStar AddCommGrpCat.{u + 1} g).obj E))) := by
  obtain ⟨U, hUd, hU⟩ := exists_dense_open_finite_scheme_splitting S g
  refine ⟨U, hUd, ?_⟩
  intro V hVU E hE
  obtain ⟨T, p, _, hpEtale, hpSurj, n, W, hcover, hdisjoint, hW⟩ := hU V hVU
  let : Etale p := hpEtale
  let : Surjective p := hpSurj
  apply isLisseEtaleSheafOfSets_of_etale_surjective_pullback p
  exact isLisse_pullback_finite_directImage_of_split_cover g V p n W
    hcover hdisjoint hW E hE

end AlgebraicGeometry.Scheme
