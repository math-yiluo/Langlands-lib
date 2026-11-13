# Split rank of an actual Tits index

This module proves the Library statement
`Langlands.GroupScheme.TitsIndexSplitRankStatement` (module
`Langlands.GroupScheme.Reductive.TitsIndexRelativeStatement`) as the theorem
`Langlands.GroupScheme.titsIndexSplitRank`. Let `k : Type u` be any field, of any
characteristic, and `u` any universe. For every Tits-index datum `d` of a field
group `G` over `k` (affine and locally of finite type), the theorem gives two
equalities in `ℕ∞`:

- the natural cardinality of the distinguished star orbits `d.DistinguishedOrbit`
  equals `splitRank G`;
- the natural cardinality of the actual simple relative roots
  `simpleRelativeRoots d.splitInclusion d.positiveCocharacter` equals
  `splitRank G`.

It also records the corollary `titsIndexRelativeStructure :
TitsIndexRelativeStructureStatement`. This pairs the published
`titsIndexStarRelativeRoots` (module `Reductive/TitsIndexStarProof`) with
`titsIndexSplitRank`. All declarations are in `Langlands.GroupScheme`. Nothing
here uses a local field, the local rank-one classification or any Kneser–Tits
statement.

## Provenance

The mathematics is the rank consequence of Tits, *Classification of algebraic
semisimple groups* (1966), §2.5.1, printed p.40 (proceedings PDF p.45),
registered as `tits-1966-classification-algebraic-semisimple`, as recorded in
the paired Markdown of the target. The facts used are these: the simple relative
roots of a semisimple group form a basis of the rational character space of a
maximal split torus, and they correspond to the distinguished orbits of the
star action. Here they are not cited from a source. The proof assembles them
from the published Library theorems named below. The individual lemmas are
internal formalization steps.

## Declarations and proof

- `IsSemisimple.subsingleton_rationalCharacters`: a semisimple field group `G`
  has at most one rational character. The published `semisimplePerfect` gives
  `derivedSubgroup G = ⊤`, so the identity `𝟙 G` is a derived-subgroup
  inclusion (`IsDerivedSubgroup`). It is closed because it is an isomorphism.
  By the published `IsDerivedSubgroup.characterRestrict_eq_zero`, every
  character restricts to zero along this inclusion. Restriction along `𝟙 G` is
  the identity (`characterRestrict_id`), so every character is zero. This
  repeats the argument used inside `IsSemisimple.relativeRoots_nonempty`
  (`Rational/IsotropicRootSubgroupGenerationProof`), stated separately here.
- `IsSemisimple.rationalCharacterRank_eq_zero`: so
  `rationalCharacterRank G = 0`, because it is the `ℚ`-rank of a subsingleton
  module.
- `TitsIndexData.card_simpleRelativeRoots_eq_splitRank`: for every
  `d : TitsIndexData G`, the natural cardinality of
  `simpleRelativeRoots d.splitInclusion d.positiveCocharacter`, cast to `ℕ∞`,
  equals `splitRank G`. The datum supplies semisimplicity (hence connected
  reductivity), the maximal split torus `d.splitInclusion` and the generic
  cocharacter `d.positiveCocharacter`. The published `relativeSimpleRootBasis`
  gives `relativeRootRank i = Nat.card (simpleRelativeRoots i ν)`. The published
  `relativeRankIdentity` gives `splitRank G = splitTorusRank T` and
  `splitTorusRank T = relativeRootRank i + rationalCharacterRank G`. The last
  summand is zero by the previous lemma. Rank zero is included: then there are
  no simple roots and both sides are `0`. This is the second conjunct of the
  target.
- `titsIndexSplitRankStatement_of_relativeSimpleRoots`: a proof of
  `TitsIndexRelativeSimpleRootsStatement.{u}` implies
  `TitsIndexSplitRankStatement.{u}`. From the second conjunct of the premise only
  the equivalence `e : d.DistinguishedOrbit ≃ simpleRelativeRoots …` is used. It
  identifies the two natural cardinalities (`Nat.card_congr`). The character
  formula on orbit classes and the first conjunct are not needed. Both
  conjuncts of the conclusion then follow from the previous lemma. The premise
  is an explicit hypothesis, not an assumed theorem.
- `titsIndexSplitRank : TitsIndexSplitRankStatement.{u}`: the reduction applied
  to the published `titsIndexRelativeSimpleRoots :
  TitsIndexRelativeSimpleRootsStatement.{u}` (module
  `Reductive/TitsIndexStarProof`). That proof does not use
  `TitsIndexSplitRankStatement`, so the argument is not circular.
- `titsIndexRelativeStructure : TitsIndexRelativeStructureStatement.{u}`: the
  pair `⟨titsIndexStarRelativeRoots, titsIndexSplitRank⟩`.
