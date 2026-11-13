# Silberger's count for explicit segment data

Author: Worker 4988. Module `Langlands.Representation.Classification.A6iiSilberger`,
namespace `Langlands.Classification.A6ii`. Internal helper for the proof of Tadić's
Corollary A.6(ii) (`IrreducibleLanglandsHeadProductProof`). It applies the published
`glRelativeRegularComparison`, the GL_n form of Silberger 1978, Lemma 5.6 (statement
`RelativeRegularComparisonStatement`). Here the fine, middle and coarse data are built
explicitly from supercuspidal representatives instead of being supplied abstractly.

## Auxiliary results

- `nonempty_innerInduced_flatten_equiv`: let `Y` be a family on the blocks of a
  flattened shape `B.flatten Q`. Inner normalized induction from the refined Levi of
  `(B, Q)` of the pulled-back block tensor of `Y` is equivalent to the block tensor over
  `B` of the blockwise normalized products `Ind_{Q i}(Y⟨i,·⟩)`. Proof: published
  `refinedInductionTensor`, `flattenedTensorRegroupEquiv` and the rank-reindexing
  equivalence `reindexRankEquiv`.
- `fineTwist_cast_cancel`: after transport along a shape equality `C = B.flatten S`,
  the fine twist of `ν^{t₀} τ` with parameter `t₀` equals the fine twist of `τ` with
  parameter `0`. Proof: substitute the equality and combine the two Levi twists by
  `leviRealPowerTwist_add`.
- `leviSquareIntegrable_admissible`: the published analytic predicate
  `IsLeviSquareIntegrable` implies admissibility. It is specialised at the Haar measure
  supplied by `glBlockCentralQuotientTopology`.

## `silbergerCount`

Inputs, for `0 < n`:

- a coarse shape `B`, a refinement `Q` with middle shape `D = B.flatten Q`, and a
  refinement `R` of `D`;
- supercuspidal representations `Asc` on the blocks of `D.flatten R`;
- irreducible, square-integrable, unitarizable representations `Zs` on the blocks of
  `D`, with surjections `Ind_{R k}(Asc⟨k,·⟩) ↠ Zs(k)` for every middle block `k`;
- a strictly decreasing exponent `b` on the blocks of `B`.

Set `π = ⊠_g Ind_{Q g}(Zs⟨g,·⟩)` and `π_t = ν^b π`. Let `ω₀` be the block tensor of the
`Asc`, and `τ` the fine twist, with parameters `0` and `b`, of `ω₀` transported along
`D.flatten R = B.flatten (B.composeRefinement Q R)`. The theorem gives `m > 0` such
that `τ` has multiplicity `m` in both the inner and the ambient opposite Jacquet
modules of `π_t`. It also gives that the induced representation of `π_t` has an
irreducible head, and that `π_t` is irreducible and admissible.

Proof. `ω₀` is irreducible and cuspidal (`glCuspidalTensor`). It is unitarized by a
real twist `ν^{t₀}` (`leviCuspidalRealUnitarization`), and `t₀` is a positive-root
parameter. That last point repeats the argument of `glDiscreteSeriesPositiveRootSupport`:
`unitaryFineTwistScalarCharacter`, `refinedQuotientOppositeCharacter`,
`refinedOppositeSquareIntegrableCone` and `positiveRootParameterCone`. The middle
representation `⊠ Zs` is irreducible, admissible and Levi square-integrable
(`glBlockTensorSquareIntegrable`, Schur's lemma for admissible irreducibles). It is a
quotient of the inner induction of the fine twist (external tensor of the given
surjections). Each `Ind_{Q g}(Zs⟨g,·⟩)` is irreducible and tempered
(`squareIntegrableBlockInduction`), so `π` is irreducible and Levi tempered
(`glBlockTensorTempered`). The fine-to-coarse surjection comes from
`normalizedNestedInduction`. Then `glRelativeRegularComparison` applies, and
`fineTwist_cast_cancel` removes the unitarizing twist from the test representation.

Source: A. J. Silberger, *The Langlands Quotient Theorem for p-adic Groups*, Math. Ann.
236 (1978), Lemma 5.6, used only through the published Library statement and proof.
