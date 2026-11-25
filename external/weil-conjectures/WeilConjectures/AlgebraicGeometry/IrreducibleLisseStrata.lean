/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.IrreducibleLisseRefinement

/-!
# Irreducible lisse strata

Source: the Weil conjectures blueprint, chapter `chap-Smooth-purity`, unit `sk-prop-sf-cbc`,
order 1602 (blueprint: lem-weil-pbc-irreducible-lisse-strata).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A constructible abelian etale sheaf on a Noetherian scheme admits a finite partition
into nonempty irreducible locally closed subschemes with finite locally constant restrictions.
Constructibility and finite local constancy are those of `def-weil-pbc-etale-sheaves`
(finite geometric stalks), applied to the underlying sheaf of sets.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc`, order 1602
(blueprint: lem-weil-pbc-irreducible-lisse-strata).

Proof:
1. By `def-weil-pbc-etale-sheaves`, choose a finite lisse stratification and discard empty
   parts. Each part is Noetherian by Stacks Tags 01OX, 01T5 and 01T6, so
   `lem-weil-pbc-noetherian-finite-components` gives finitely many irreducible components.
2. Order these components and subtract from each the union of earlier components. Each
   difference is open in its component and contains its generic point: irreducibility
   prevents a component from being covered by the finitely many other components. Hence
   each difference is nonempty and irreducible. The differences are disjoint, cover the
   original part, and are locally closed in X. Give them their reduced induced scheme
   structures (Tag 01J4); their composite immersions into X are immersions (Tag 02V0),
   as required by `definition-ind-etale-pro-etale-weakly--3`.
3. Apply `lem-weil-pbc-pullback-finite-locally-constant` to the immersion of each difference
   into its original part and that part's immersion into X. Pullback preserves finite
   local constancy and composes, so all the resulting restrictions are lisse. Combining
   the finitely many refinements gives the required partition. -/
theorem exists_irreducible_lisse_stratification
    (X : Scheme.{u}) [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsConstructibleEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F)) :
    ∃ S : Stratification X, ∀ i : Fin S.n,
      IrreducibleSpace (S.domain i) ∧
        IsFiniteLocallyConstantSheafOfTypes
          ((etaleSetPullback (S.immersion i)).obj
            ((sheafCompose X.smallEtaleTopology
              (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F)) := by
  rcases hF with ⟨S, hS⟩
  exact exists_irreducible_refinement X
    ((sheafCompose X.smallEtaleTopology
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F) S hS

end AlgebraicGeometry.Scheme
