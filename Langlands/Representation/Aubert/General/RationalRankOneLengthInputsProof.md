# Rational rank-one length two from detection and Jacquet-length inputs

Author: Worker 3915.

`Langlands.Aubert.General.RationalPointFamily.rationalRankOneLengthTwoFromInputs`
proves the whole proposition
`RationalRankOneLengthTwoFromInputsStatement.{u, v}` from
`Langlands.Representation.Aubert.General.RationalRankOneLengthInputsStatement`.
It introduces no theorem parameters outside that proposition, and the field
and carrier universes `u` and `v` stay independent. The statement pair, the
target pair `RationalCorollaryTargets` and every pair they import are
unchanged.

The proposition is an implication. Assuming
`RationalMaximalCuspidalJacquetDetectionStatement.{u, v}` and
`RationalMaximalCuspidalJacquetBudgetStatement.{u, v}`, it concludes
`RationalRankOneLengthTwoStatement.{u, v}`. This proof does not prove either
input, so it does not prove the target. It shows that the two inputs are the
only missing representation-theoretic ingredients.

## Generic length bound

`Langlands.Aubert.General.repLength_le_two_of_jacquetFamily` works in any
locally compact nonarchimedean topological group `H`. It takes a finite index
type `Idx` and, for each index `b`, an actual semidirect decomposition
`h b` of `P b = M b ⋉ U b` with closed radical `U b`. Each `U b` is a limit of
compact subgroups (`Jacquet.Localization.IsLimitOfCompactSubgroups`), in the
sense that every compact subset lies in a compact subgroup. Let `A` be a
smooth complex representation of `H`. Assume that:

- the sum over `b` of the composition lengths `repLength` of the actual
  normalized Jacquet modules `r_b A` (`jacquetFunctor (h b) (hU b)`) is at
  most two in `ℕ∞`;
- every actual irreducible subquotient `D` of `A` has a nontrivial `r_b D`
  for some `b`.

Then `repLength A.representation ≤ 2`. The proof runs as follows.

1. Each `r_b` maps actual short exact sequences to short exact sequences, by
   the published `jacquetFunctor_map_isShortExact` with the compact-limit
   hypothesis. Its three conclusions are rearranged into the published
   predicate `Derivative.Mirabolic.MapsShortExactIntertwiners`.
2. Each summand is at most the total sum (`Finset.single_le_sum`), hence at
   most two. In particular it is finite, so its natural-number value `bnd b`
   (`ENat.toNat`) casts back to it exactly (`ENat.natCast_toNat`).
3. Casting the natural sum of the `bnd b` gives the `ℕ∞` sum
   (`Nat.cast_sum`). The budget hypothesis therefore gives `∑ b, bnd b ≤ 2`
   in `ℕ`.
4. The published `Langlands.exactFamilyLengthBound`, applied to the family
   `r_b` with bounds `bnd b` and the detection hypothesis, gives an actual
   composition series of `A` with `m ≤ ∑ b, bnd b` simple factors.
5. The published `repLength_eq_of_hasSimpleFactors` identifies `repLength` of
   `A` with `m`, so `repLength A.representation ≤ 2`.

Finite length of `A` is not assumed.

## The rational implication

`rationalRankOneLengthTwoFromInputs` introduces the target's binders exactly
as stated. As in the target, it installs `pointTopology`, the finite
simple-root enumeration `simpleRelativeRootFintype` and classical
`DecidableEq`. It then takes a maximal standard `J`, an irreducible
finite-length `σ` on `levi i ν J`, its inside-Levi cuspidality `hcusp` and
reducibility `hred` of the actual normalized induction `A = i_J σ.val`.

- Irreducibility of `σ.val` makes its group-algebra module simple, hence
  nontrivial (`IsSimpleModule.nontrivial`).
- The published proof `rationalStandardInductionNonzero` then makes `A`
  nontrivial.
- The generic bound is applied with `Idx = SimpleRoot i ν`. For index `β`,
  the family is the actual `parabolic i ν`, `levi i ν` and `unipotent i ν` at
  `Finset.univ.erase β`, with decomposition
  `isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν (Finset.univ.erase β)`
  and closedness `hU (Finset.univ.erase β)`. The published
  `standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`
  supplies the compact-limit property of each radical from `hStandard`, `hG`,
  `hi` and `hν`. So no compact-limit or exactness premise is added.
- The budget hypothesis and the detection hypothesis are the two inputs,
  instantiated at the same field, group, torus, cocharacter, premises, `J`,
  `σ.val`, `hσ` and `hcusp`. They have exactly the shapes required by the
  generic bound, so `repLength A.representation ≤ 2`.
- The published `exists_hasTwoConstituents_of_length_le_two`, applied to the
  nontrivial `A`, this bound and `hred`, gives two actual finite-length
  irreducible factors and an actual short exact sequence. That is
  `HasTwoConstituents` in its first order. No splitting or semisimplicity is
  assumed or produced.

## Dependencies

The proof uses these published declarations:

- `jacquetFunctor_map_isShortExact`;
- `standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`;
- `exactFamilyLengthBound` and `repLength_eq_of_hasSimpleFactors`;
- `rationalStandardInductionNonzero`;
- `exists_hasTwoConstituents_of_length_le_two`;
- the standard-family adapters `isSemidirectDecomposition_of_standardCocharacterStatement`
  and `isSemidirectDecomposition_in_levi`.

It also uses elementary `ℕ∞` arithmetic from Mathlib. The compact-limit
adapter rests on the published `BruhatTits.dynamicUnipotentCompactOpenContainment`.

The proof body invokes no Langlands classification, character independence,
geometric lemma, adjointness or cuspidal-support theorem. Those enter only
through the two hypotheses. A future proof of the budget input needs the
geometric lemma. A proof of the detection input through
`rationalMaximalCuspidalJacquetDetectionFromExtraction` needs the published
factor-extraction proposition, whose own proof needs the geometric lemma.
Such proofs must record their own dependencies. The final assembly would
apply this theorem to them.

The checked lean_check diagnostic `40286eac-56fc-459a-abc8-7a6782f6df66`
reports zero errors and warnings and only the axioms `propext`,
`Classical.choice` and `Quot.sound`.
