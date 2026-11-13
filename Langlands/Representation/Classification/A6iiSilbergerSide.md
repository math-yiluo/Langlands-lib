# The Silberger side of the head comparison

Author: Worker 4988. Module `Langlands.Representation.Classification.A6iiSilbergerSide`,
namespace `Langlands.Classification.A6ii`. Internal helper for the proof of Tadić's
Corollary A.6(ii) (`IrreducibleLanglandsHeadProductProof`).

## Helpers

- `count_congr`: multiplicities move along equivalences of the ambient representation
  and of the test representation (`equivJordanHolderMultiplicityTransport`).
- `realPowerTwist_conj` and `twistSC_conj`: `ν^a ν^j ν^{-b} ρ = ν^j ρ` when `a = b`.

## Definitions

Let `c` be a segment datum and `m` a merge grouping of its segments. Its groups form the
shape `Bc`, its segment refinement `Q` gives the middle shape `D = Bc.flatten Q`
(`A6iiDatum`), and the merged datum is `merged c m`.

- `segmentRefinement c m`: cuts the block of each merged segment `Δ` into
  `len Δ` blocks of size `rank Δ` (`BlockShape.uniform`).
- `fineShape c m = D.flatten (segmentRefinement c m)`: all supercuspidal blocks in
  merged order.
- `fineAtoms F T c m A`: the block tensor over `fineShape c m` whose block for the
  `j`-th member of the merged segment `l` is `ν^j A_l`. Here `A_l` is the given
  supercuspidal representative of segment `l` (`twistSC`).

## `silbergerSide`

Hypotheses, for `0 < n`:

- `A_l` are supercuspidal representatives and `c.blocks l` are irreducible quotients of
  `i(A_l, νA_l, …)`;
- `u l` are unitary exponent data of the blocks, the merge exponents are
  `(u l).exponent`, and the normalized blocks `ν^{-(u l).exponent} c.blocks l` are
  square-integrable;
- `L` is an irreducible quotient of `(merged c m).induced`.

Conclusion: there is `m₀ > 0` such that `fineAtoms` has multiplicity `m₀` in the opposite
Jacquet module along `fineShape c m` of `(merged c m).induced`, and a multiplicity at
least `m₀` in that of `L`.

Proof.

1. Apply `silbergerCount` to the following data:
   - coarse shape `Bc`, middle refinement `Q`, fine refinement `segmentRefinement`;
   - supercuspidals `Asc = ν^j ν^{-e_l} A_l`, where `e_l` is the exponent of segment `l`;
   - normalized blocks `Zs = ν^{-e_l} c.blocks l`, which are irreducible,
     square-integrable, and unitarizable by `normalized_unitarizable`;
   - quotient maps from `segment_twisted_quotient`;
   - the strictly decreasing group exponents `b = m.exponent`.

   The outer twist is moved inside the blocks (`leviRealPowerTwist_blockTensor`). Group
   `g` has exponent `b_g = e_l` for each of its members (`label_exponent`), so
   `commonExponentIso` and `nonempty_flatten_iso` identify the coarse induced
   representation with `(merged c m).induced`.
2. The ambient count passes to the opposite Jacquet module along `Bc.flatten S`
   (`count_flattened`). `quotient_count_ge` gives the bound for `L`.
3. Both counts are transported to `fineShape c m`:
   - `compSymmCompEquiv` undoes the flattened Levi equivalence;
   - `count_cast` handles the shape equality `flatten_composeRefinement`, where the
     exponents match by `outer_composeRefinement`;
   - finally `ν^{b_g} ν^j ν^{-e_l} A_l = ν^j A_l` blockwise (`twistSC_conj`), which
     gives exactly `fineAtoms`.
