# The rank-one stage of Henniart's induction

Author: Worker 4803. Module `Langlands.Correspondence.HenniartRankOneStageProof`,
namespace `Langlands.Henniart.Extension`. Universes: `uK` (p-adic fields), `uW`
(Weil carriers), `uV` (supercuspidal carriers), `uE` (local-constant values in
the candidate properties), all independent.

## Main result

`rankOneStage_of_reciprocity` proves

`CandidateExistenceStatement.{uK, uW, uV, uE, uK} →
LocalClassField.CommonClosureReciprocityExistence.{uK} →
RankOneStageStatement.{uK, uW, uV, uE}`.

`RankOneStageStatement` (module `HenniartStableMapStatement`) says that for every
prime `p` and every `K : PadicField.{uK} p`, both `StableExistsAt K 1` and
`StableSurjectiveAt K 1` hold. Both hypotheses are published Library statements.
The theorem asserts neither. Local reciprocity is used only to obtain a
geometric reciprocity candidate `e` of `K` (`baseGeometricReciprocityProof`).

## Supporting results

For a p-adic field `K`, a geometric reciprocity candidate `e` and a field
character `χ : QuasiCharacter K`:

- `PadicSupercuspidal.includeUnitary_generator`: including the generator of a
  unitary supercuspidal class gives the generator of the underlying class.
- `twist_trivialWeilBasis`: twisting the trivial rank-one Weil class by
  `χ ∘ rec` gives `rankOneWeilCharacterClass K e χ`.
- `norm_eq_one_of_rankOne_isUnitary`: if `rankOneWeilCharacterClass K e χ` is
  unitary, then `‖χ a‖ = 1` for every unit `a`.
- `candidate_rankOne`: let `Φ` be a map with `LatticeMap.HenniartProperties`, and
  let `‖χ‖ = 1`. If `x` in the domain of `Φ` is the generator of the unitary class
  `⟨1, rankOneWeilCharacterClass K e χ⟩`, then `Φ x` is the generator of the unitary
  class `⟨1, rankOneSupercuspidalClass K χ⟩`.
- `isStableImage_rankOne`: under candidate existence, if that rank-one Weil class
  factors through a finite quotient, its stable image is the generator of the
  `GL₁` class of `χ`.
- `rankOne_isFiniteFactoring`: if `χ ^ N = 1` for some `N > 0`, the rank-one Weil
  class of `χ` factors through a finite quotient of the absolute Galois group.
- `rankOneWeil_isUnitary`: if `‖χ‖ = 1`, the rank-one Weil class of `χ` is unitary.
- `rankOneSupercuspidalClass_centralActsBy_unique`: if a unit `a` acts on the
  `GL₁` class of `χ` by the scalar `c`, then `c = χ a`.
- `stableExistsAt_one` and `stableSurjectiveAt_one`: `StableExistsAt K 1` and
  `StableSurjectiveAt K 1` under candidate existence and a geometric `e`.

## Provenance

Internal proof of the published `RankOneStageStatement`. In Henniart (2000),
§4.1 and §4.3 (printed p. 452, PDF p. 14), the rank-one case is clear: for a
finite-order `σ` of dimension one, `π(σ)` is the character of `F^×` with
`π(σ) ∘ τ_F = σ`. In the Library this comes from the character clause of the
candidate properties (`LatticeMap.CharacterCompatibility`, Henniart 2000, 3.8).

## Proof

- Rank-one Weil classes are the classes `rankOneWeilCharacterClass K e χ`
  (`rankOneWeilCharacterClass_surjective`). Such a class is the twist of the
  trivial class by `χ ∘ rec` (`IsRankOneWeilCharacter.twist`, `class_unique`).
  So if it is unitary, `‖χ ∘ rec‖ = 1` by
  `Weil.norm_eq_one_of_isUnitaryClass_twist`, and `‖χ‖ = 1` because `rec` is
  surjective (`reciprocityHom_surjective'`). Conversely, if `‖χ‖ = 1`, it is the
  unitary twist `weilUnitaryTwist K e χ` of the trivial unitary class.
- Existence. The character clause of a candidate gives an element `x'` in its
  domain whose inclusion is the generator of the rank-one Weil class of `χ`, and
  whose image is the generator of the `GL₁` class of `χ`. Inclusion of unitary
  lattices is injective (`Weil.includeUnitary_injective`), so `x'` is the element
  representing `σ`. Its image is the generator of a unitary class
  (`IsCandidate.exists_generator`). That class is the `GL₁` class of `χ`, since
  `Finsupp.single` is injective. This holds for every candidate, so the stable
  image exists and is this class.
- Surjectivity. A unitary `GL₁` class is `rankOneSupercuspidalClass K χ`
  (`rankOneSupercuspidalClass_surjective`). Its central character is `χ`, so `χ`
  has finite order `N`, and `‖χ‖ = 1` (`Complex.norm_eq_one_of_pow_eq_one`). The
  one-dimensional representation `χ ∘ rec` is continuous and its image lies in
  the `N`-th roots of unity, so it has finite image. By
  `Weil.Local.localWeilGaloisTypeFor` it is of Galois type, and
  `LocalWeil.exists_finiteQuotient_of_isLocalGaloisType` gives a finite quotient
  through which it factors. Existence then gives its stable image, the `GL₁`
  class of `χ`.

Standard axioms only.
