# The real Langlands classification starting from a principal-series quotient

`Langlands.Archimedean.realLanglandsFromPrincipalSeries` proves the Library's
`RealLanglandsFromPrincipalSeriesStatement.{uV}` from `RealLanglandsQuotientReduction`.
For every `n` and every irreducible admissible real `(𝔤𝔩_n(ℝ), O(n))`-module on a complex
vector space `V : Type uV`, the input includes a list `cs` of `n` real characters and a
nonzero standard intertwiner from the `O(n)`-finite principal series of `cs` to `V`.
The theorem gives a list `ds` of total rank `n`, in non-increasing order of the real parts
of the block exponents, and a nonzero standard intertwiner from the `O(n)`-finite part of
`realStandardModule n ds` to the same `V`. The input order is arbitrary. There are no
additional hypotheses.

## Proof

1. **Filtrations at an adjacent inversion.** The published `realCharacterPairFiltration`
   handles two characters via the rank-two block Frobenius maps. At a nonresonant exponent
   difference it uses an exact swap; in the resonant case it also uses a rank-two induction
   block. The published `realInducedPairFiltration` handles the remaining block types: the
   two orders of a character and an induction block on `GL₃(ℝ)`, and two induction blocks on
   `GL₄(ℝ)`. `InductionStages.realAdjacentFiltrationInStages` lifts the latter filtrations past
   the prefix and suffix blocks by averaging the maps on the small compact group and inducing
   them using the normalized block slices. See [the character-pair proof](RealCharacterPairFiltration.md)
   and [the induced-pair proof](RealInducedPairFiltrationProof.md).
2. **A new nonzero intertwiner.** `realRankOneStep_of_filtration` picks the first filtration
   map `q j` with `B ∘ₗ q j ≠ 0`; one exists because the ranges span. The earlier ranges lie in
   `ker B`, so the composition intertwines right translations and right derivatives exactly,
   even though `q j` intertwines them only modulo the earlier ranges. The source list either
   exchanges the two adjacent blocks or replaces them with blocks whose complex exponent
   support is a permutation of the old support and whose sum of squared weights is strictly
   larger. This is the exchange-or-replacement step of [the filtration reduction](RealRankOneStepFiltration.md).
3. **Termination.** `realLanglandsFromPrincipalSeries_of_rankOneStep` starts with
   `cs.map RealBlock.character` and the given map. The length of its exponent support is `n`,
   and the support remains a permutation of that initial support `S₀`. This keeps the total
   rank `n` and bounds the sum of squared weights `W` by the natural floor
   `K = ⌊2 ∑_{s ∈ S₀} (Re s)²⌋₊` (the sum counts multiplicities). The Lean proof uses nested
   strong induction on `K - W` and the inversion count. An exchange keeps `W` and removes
   an inversion; a replacement increases `W` and strictly decreases `K - W`. If the list is
   not ordered, there is a strict adjacent inversion. At the ordered list the current map
   is nonzero and intertwines both actions, so it is the required witness. See
   [the rank-one reduction](RealLanglandsRankOneReduction.md).

The Lean term applies the reduction in step 3 to the theorem in step 2 with both proofs
from step 1. It does not invoke a classification theorem or a composition series as an input.

## Model and scope

All the filtrations and intertwiners are constructed on the actual scalar-function model,
not transferred from another realization. As described in [StandardModule.md](StandardModule.md),
this is the normalized induced model in stages: use the Borel modulus factor in the scalar
principal series and cut out each `GL₂(ℝ)` block by its left-rotation Fourier conditions.
The compact slice and evaluation at the identity in [RealInductionStagesSlice.md](RealInductionStagesSlice.md)
implement the function-level operation of induction in stages used here. The imported
[RealStandardModuleGKModule](RealStandardModuleGKModule.md) proves closure of the `O(n)`-finite
part under both actions and identifies those actions (`realStandardRep`, `realStandardLie`)
with right translation and complexified right differentiation. No comparison with a separate
Hilbert-space globalization is used or proved by this assembly.

This gives the existence conclusion of the real Langlands classification in the form needed
when a principal-series quotient is already supplied, with the chamber convention of
[RealGenericParameterReduction.md](RealGenericParameterReduction.md). It does not prove that
every irreducible admissible module is a principal-series quotient, nor does it assert
uniqueness of the ordered parameters or of the irreducible quotient of a standard module.
