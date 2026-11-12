# Restriction of rational characters to a split component

Author: Worker 33 (Task 3798, `6d0882ee-6e45-410c-b5a1-86d4544a4ffb`).

`Langlands.GroupScheme.characterRestriction` proves exactly the published
proposition `Langlands.GroupScheme.CharacterRestrictionStatement.{u}` (module
[`CharactersStatement`](CharactersStatement.md)), at every universe `u`, with
no hypotheses.

For every field `k : Type u`, every connected reductive group scheme `G` over
`Spec k`, and every split component `i : A.toGrp ⟶ G` (`IsSplitComponent i`),
the restriction map `characterRestrict i : rationalCharacters G →+
rationalCharacters A.toGrp` is injective and its range has finite index. The
field is arbitrary: no perfectness, characteristic, splitness or local-field
hypothesis is added to the statement.

## Implemented proof

The Lean proof is one application:

`characterRestriction_of_torusSurjectivity reductiveCentralTorusSurjectivity.{u}`.

- `characterRestriction_of_torusSurjectivity`, from
  [`CharacterRestrictionReduction`](CharacterRestrictionReduction.md), has type
  `ReductiveCentralTorusSurjectivityStatement.{u} → CharacterRestrictionStatement.{u}`.
  It obtains, in turn, a central torus and derived subgroup whose product map
  is an epimorphism, that central tori detect nonzero rational characters,
  that central split tori detect them, and finally injectivity (published
  `characterRestrict_injective_of_centralSplitTorusCharacter`) together with
  finite index (published `IsSplitComponent.finiteIndex_range_characterRestrict`).
  Its Markdown describes each step.
- `reductiveCentralTorusSurjectivity`, from
  [`CentralTorusSurjectivityProof`](../Reductive/CentralTorusSurjectivityProof.md),
  is the published unconditional proof of
  `ReductiveCentralTorusSurjectivityStatement.{u}`: a closed central torus and
  any derived-subgroup inclusion of a connected reductive field group have a
  surjective product map.

## Relation to the literature

The statement corresponds to Renard V.2.6 and Waldspurger I.1 (see the
statement's Markdown). The implemented route detects a nonzero rational
character on a central split torus, as in J. S. Milne, *Algebraic Groups*
(2017), Proposition 21.61 and Exercises 12-5 and 12-6; finite index of the
range is the separately published finite-index result.

## Axioms

`lean_check` reports only `propext`, `Classical.choice` and `Quot.sound`.
