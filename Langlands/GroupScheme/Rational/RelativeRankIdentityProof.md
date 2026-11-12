# Intrinsic split-rank and rational-character rank identities

Author: Worker 3893 (Task 3893, `9548db09-113b-4d98-89df-2b8794fd75cf`).

`Langlands.GroupScheme.relativeRankIdentity` proves exactly the published
proposition `Langlands.GroupScheme.RelativeRankIdentityStatement.{u}` (module
[`RelativeRankStatement`](RelativeRankStatement.md)), at every universe `u`, with
no hypotheses.

For every field `k : Type u`, every connected reductive group scheme `G` over
`Spec k` and every actual maximal split torus `i : T.toGrp ⟶ G`, the statement
asserts:

- `ℚ ⊗[ℤ] characterLattice T`, the relative root span `relativeRootSpan i` and
  `ℚ ⊗[ℤ] rationalCharacters G` are finite-dimensional over `ℚ`;
- the split rank of `G` equals the split-torus rank of `T`;
- `splitTorusRank T = relativeRootRank i + rationalCharacterRank G`;
- for every actual split component `a : A.toGrp ⟶ G`, `ℚ ⊗[ℤ] characterLattice A`
  is finite-dimensional, the rationalized restriction
  `rationalCharacterRestrictRat a` is bijective,
  `rationalCharacterRank G = splitTorusRank A`, and
  `splitTorusRank T = relativeRootRank i + splitTorusRank A`.

The field is arbitrary, nonreduced relative root systems and rank zero are
included, and no basis, rank, complement or conjugacy conclusion is assumed.

## Implemented proof

The Lean proof is one application:

`relativeRankIdentityStatement_of_complement_restriction_conjugacy
relativeCharacterRootComplement characterRestriction maximalSplitTorusConjugacy`.

- `relativeRankIdentityStatement_of_complement_restriction_conjugacy`, from
  [`RelativeRankReduction`](RelativeRankReduction.md), has type
  `RelativeCharacterRootComplementStatement.{u} → CharacterRestrictionStatement.{u} →
  MaximalSplitTorusConjugacyStatement.{u} → RelativeRankIdentityStatement.{u}`.
  It uses restriction injectivity on a split component, transported to the maximal
  split torus through a chosen factorization of the split component, to make the
  rationalized restriction from `X*(G)` to `X*(T)` injective; the root/character
  complement then splits `ℚ ⊗ X*(T)` and gives the rank sum; conjugacy identifies
  `splitRank G` with `splitTorusRank T`; and, for each split component, the
  integral restriction facts (injective, finite-index range) give bijectivity of
  the rationalized restriction and `rationalCharacterRank G = splitTorusRank A`,
  which substituted into the rank sum gives the last clause. Its Markdown
  describes each step.
- `relativeCharacterRootComplement`, from
  [`RelativeCharacterRootComplementProof`](RelativeCharacterRootComplementProof.md),
  is the published proof of `RelativeCharacterRootComplementStatement.{u}`: the
  relative root span complements the restricted rational characters over `ℚ` and
  over `ℝ`.
- `characterRestriction`, from
  [`CharacterRestrictionProof`](CharacterRestrictionProof.md), is the published
  proof of `CharacterRestrictionStatement.{u}`: restriction of rational characters
  to a split component is injective with finite-index range.
- `maximalSplitTorusConjugacy`, from
  [`MaximalSplitTorusConjugacyProof`](MaximalSplitTorusConjugacyProof.md), is the
  published proof of `MaximalSplitTorusConjugacyStatement.{u}`: maximal split tori
  are rationally conjugate and every finite splitting of one has cardinality equal
  to the split rank.

## Relation to the literature

The statement's Markdown gives its sources. The implemented route follows them:
rational conjugacy of maximal split tori (Borel–Tits 4.21 and 4.23), the
complement of the relative root span and the restricted rational characters in
`ℚ ⊗ X*(T)` (the root rank equals the semisimple split rank, Borel–Tits
Theorem 5.3), and injective finite-index restriction of rational characters to
the split component (Renard V.2.5–6), passed to `ℚ` by scalar extension.

## Axioms

`lean_check` reports only `propext`, `Classical.choice` and `Quot.sound`.
