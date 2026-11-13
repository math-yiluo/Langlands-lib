# The two ends of the gallery, and helpers for the assembly

Author: Worker 5120.

This module proves the start and end steps of the gallery argument for
`InducedTwistQuotientPersistenceStatement`, a split-torus factorization, and small
helpers. All declarations are in `Langlands.InducedTwistPersistence`.

## Helpers

- `pointImage_eq_inf_of_range_eq_inf`: an equality `range x = range y ⊓ range z` of
  subgroup functors gives the same equality of rational point images.
- `exists_compact_openSubgroup_le`: in a locally compact nonarchimedean group, compact
  open subgroups are cofinal among open subgroups.
- `twist_eq_of_eq`: twisting by equal characters gives equal representations.
- `intertwiningMap_ne_zero_of_injective`: an injective intertwiner out of a nonzero space
  is nonzero.
- `exists_isGeneralizedEigencharacter_of_isAdmissible`: an irreducible admissible
  representation has an exponent on every central subgroup. By the published
  `admissibleSchur_centralCharacter` the centre acts by a character. Restricting it gives
  an eigencharacter (`isGeneralizedEigencharacter_of_eigenvector`).

## Split components

`exists_splitComponent_factor`. Let `M` be connected reductive, `q : Q ⟶ M` a parabolic
with rational Levi `lQ : L ⟶ Q`, and `a : A ⟶ M` a split component. Then there are:

- a split component `b_L : B ⟶ L`;
- a split subtorus `b : A ⟶ L`, central in `L`, with `b ≫ lQ ≫ q = a`;
- a map `e : A ⟶ B` with `e ≫ b_L = b`.

Proof. `L` has a split component (published `exists_isSplitComponent`). Its centralizer in
`M` is `L`, by the published `IsSplitComponent.torusCentralizer_comp_eq_of_parabolicDynamic`
with `parabolicDynamic`. The image of `a` is central, hence lies in that centralizer
(`center_le_torusCentralizer`). So it factors through the closed subgroup `L`
(`IsSplitSubtorus.factorInClosedSubgroup`). Centrality descends along the monomorphism
(`IsCentral.of_comp`). The published `IsSplitComponent.exists_factor` gives `e`.

## Start

`persistenceInvariant_opposite`. The data are:

- `P = MN` with an opposite `P̄ = M N̄` (`mbar ≫ pbar = l ≫ p`, and
  `p(P(k)) ∩ pbar(P̄(k)) = (l ≫ p)(M(k))`);
- a parabolic `Q = LV` of `M`;
- a parabolic `R` of `G` with `lR ≫ r = lQ ≫ q ≫ l ≫ p`, `R ≤ P̄` and `R ∩ M = Q`;
- second adjointness (`LeviSecondAdjointnessStatement.{u, v}`), a central `b_L`, an
  irreducible admissible `τ` of `M(k)`, an irreducible `Y` of `L(k)`, a nonzero
  `f : τ → i^M_Q(Y)`, and an exponent `χ` of `b_L` on `Y`.

Then `PersistenceInvariant (lQ ≫ q ≫ l ≫ p) b_L (i_P(τ)/S) χ (range r)` holds for every
invariant subspace `S ≠ ⊤`.

Proof. Second adjointness and `exists_injective_oppositeJacquet_of_quotient` give an
injection `τ ↪ r_P̄(i_P(τ)/S)`. Lift the carrier with `SmoothRep.universeLift`, so that
`r^M_Q` applies to both sides at universe `max u v`. Frobenius reciprocity
(`isGeneralizedEigencharacter_jacquet_of_ne_zero_induction`) puts `χ` into
`r^M_Q(universeLift τ)`. Exactness (`leviJacquetFunctor_map_injective`) carries it into
`r^M_Q(r_P̄(i_P(τ)/S))`. The published `leviParabolicTransitivity` identifies the latter
with `r_R(i_P(τ)/S)`.

## End

`isGeneralizedEigencharacter_of_persistenceInvariant`. Let `F ≤ range p` with
`range (q ≫ l ≫ p) = range (l ≫ p) ⊓ F`. Let `a`, `b_L` be split components and
`e ≫ b_L ≫ lQ ≫ q = a`. Then for admissible `Z`, the invariant at `F` with exponent `χ`
implies that `χ ∘ e` is an exponent of `a` on `r_P(Z)`.

Proof. The invariant supplies an actual `R` with range `F`. Transitivity gives
`r_R ≅ r^M_Q ∘ r_P`, so `χ` is an exponent of `r^M_Q(r_P(Z))`. Here `r_P(Z)` is
admissible (`arbitraryParabolicJacquetAdmissibility`), and
`isGeneralizedEigencharacter_of_leviJacquet_restrict` (Renard VII.1.1 (ii)) restricts the
exponent to `A_M`.

## Provenance and boundary

These are the start and end steps of the derived second-adjointness route to Konno 2003,
Theorem 4.2. Second adjointness is the hypothesis `hadj`, the published proof target
`LeviSecondAdjointnessStatement`. Everything else is a published theorem.
