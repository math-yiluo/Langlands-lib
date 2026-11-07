# Ordered unramified principal series: reduction to rank one

Author: Worker 1789.

This module reduces the published
[`OrderedUnramifiedPrincipalSeriesLPolynomialStatement`](SphericalStandardLPrerequisites.md)
to a single explicit rank-one input. It does not prove that input. All
declarations are in `Langlands.Correspondence.OrderedUnramifiedPrincipalSeries`.
As in `PadicPairFactors`, the field topology, valuation, local-field structure
and the topology on `GL_n(F)` are the canonical local instances of the
supplied p-adic field `F`.

## Declarations

- `block F z` is the rank-one representation
  `characterRepresentation (determinantQuasiCharacter F 1 (Unramified.character F z))`
  of the unramified character with uniformizer value `z`, and
  `trivialBlock F` is the trivial character
  `characterRepresentation (determinantQuasiCharacter F 1 1)` of `GL₁(F)`.
  The latter is literally the test representation of the target statement.
  `block_isOfWhittakerType` and `trivialBlock_isOfWhittakerType` record their
  full Whittaker type from `rankOneCharacter_isOfWhittakerType`.
- An `example` checks by `rfl` that `Unramified.principalSeriesOfTuple F z`
  is the canonical normalized induction of the blocks `block F (z i)` along the
  upper-Borel shape `succBlockShape (fun _ => 0) (borel_sum r)`.
- `RankOneLPolynomialInput F` is the proposition that, for every unitary
  additive character `ψ`, every additive Haar measure `μ` and every `z : ℂˣ`,
  any polynomial `P` with
  `IsPadicSymmetricLPolynomial F ψ μ (block F z) (trivialBlock F) P`
  equals `1 - C z * X`. It quantifies over all `ψ` and all `μ`, not only
  self-dual pairs, because the dual step below changes `ψ` to `ψ.scale (-1)`
  while keeping the measure. This is an internal interface: it is the
  rank-one (`GL₁ × GL₁`, Tate) case of the target, phrased for the single
  character rather than a principal series of length one.
- `exists_tail_dvd` (for a tuple `z` of length `b + 2`, a unitary additive
  character `ψ` and a self-dual Haar measure
  `ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ`):
  a certified L-polynomial `P` of
  `principalSeriesOfTuple F z` against `trivialBlock F` is divisible by some
  certified L-polynomial of `principalSeriesOfTuple F (Fin.tail z)` against
  `trivialBlock F`.
- `inverseTransposePullback_block` and `inverseTransposePullback_trivialBlock`:
  pulling `block F z` back along inverse transpose gives `block F z⁻¹`, and the
  trivial block is unchanged.
- `eq_prod_of_tail_dvd` (assuming `RankOneLPolynomialInput F`): if `z` has
  length `b + 1` with weakly increasing absolute values, `P` is a certified
  L-polynomial of `principalSeriesOfTuple F z` against `trivialBlock F`, and
  `∏ i : Fin b, (1 - C (z i.succ) * X)` divides `P`, then
  `P = ∏ i, (1 - C (z i) * X)`.
- `eq_prod_of_certificate` (assuming `RankOneLPolynomialInput F`): every
  certified L-polynomial of an ordered tuple against `trivialBlock F` equals
  `∏ i, (1 - C (z i) * X)`.
- `orderedUnramifiedPrincipalSeriesLPolynomial_of_rankOne` (assuming
  `RankOneLPolynomialInput F`) proves
  `OrderedUnramifiedPrincipalSeriesLPolynomialStatement.{uF} F`.

## Proof

**Tail divisibility.** For a tuple of length `b + 2`, the published
`inducedTailLFactor` applied to the first block `block F (z 0)`, the
principal series of the tail and the trivial test block gives certified
polynomials `Pfull` and `Ptail` with `Ptail ∣ Pfull`. The tail principal
series has full Whittaker type by `normalizedProductWhittakerType`.
`Pfull` certifies the two-block induction `Shahidi.twoBlocks 1 (b + 1)`
of the `ULift`-conjugated first block and tail. To identify it with `P`,
the proof transports the certificate of `P` along a chain of actual
equivalences, each by `IsPadicSymmetricLPolynomial.congr_equiv`:

1. `headTailProductInductionEquiv` regroups the upper-Borel induction into
   the head block and the induced tail;
2. `Padic.normalizedProductInducedEquiv_of_sizes` replaces the two factors by
   the `ULift`-conjugated first block and tail principal series, using
   `universeLiftEquiv`, `normalizedProductRankCastEquiv` and the `ULift`
   conjugation equivalence `uliftConjEquiv`;
3. `normalizedProductRankCastEquiv` and `symmetricLPolynomial_rankCast`
   remove the rank cast `0 + 1 + b = b + 1`;
4. `successorPairInducedEquiv` identifies the successor-indexed pair family
   with the literal `Shahidi.twoBlocks`/`Shahidi.pairFamily` induction.
   It is a local copy of the private construction in
   `InducedTailConditionalAssemblyProof`, specialized to a rank-one first
   block.

Certificate uniqueness (`IsPadicSymmetricLPolynomial.unique`) then gives
`Pfull = P`.

**Dual blocks.** The determinant of the inverse transpose of `g ∈ GL₁` is
`(det g)⁻¹` (`RankOneGammaTwist.determinant_inverseTranspose`), and
`Unramified.character F z` evaluated at `x⁻¹` is the value of
`Unramified.character F z⁻¹` at `x`. This gives
`inverseTransposePullback (block F z) = block F z⁻¹`. The trivial block is
fixed by `rfl`.

**Reflection step.** The proof of `eq_prod_of_tail_dvd` uses the published
two-family data for the family of `b + 1` blocks `block F (z i)` against the
single family `trivialBlock F`. From
`TemperedLFactorDivisibility.twoFamilyLPolynomialData` it gets `d`, from
`TemperedLFactorDual.nonempty_dualTwoFamilyLPolynomialData` it gets the dual
data `e`, and from `TemperedLFactorGamma.nonempty_reflectedRatioData` it gets
the gamma ratio data `g`.

- Uniqueness, with `singleBlock_L_iff` on the one-block second family, gives
  `P = d.inducedPolynomial`.
- The rank-one input gives every original block polynomial `1 - C (z i) * X`.
  The dual block certificates use `ψ.scale (-1)` and the pulled-back blocks.
  After the dual-block rewrites, the input gives every dual block polynomial
  `1 - C (z i)⁻¹ * X`.
- The residual factorization of `d` reads
  `∏ i, (1 - C (z i) * X) = D * P`. Writing `P = (∏ i : Fin b, (1 - C (z i.succ) * X)) * S`
  and cancelling the nonzero tail product gives `1 - C (z 0) * X = D * S`.
  Hence `D` has no root in the open disk of radius `‖z 0‖⁻¹`.
- Since `‖z 0‖ ≤ ‖z i‖` for all `i`, the dual block product, and hence the
  dual residual `E`, has no root in the open disk of radius `‖z 0‖`.
- Both induced polynomials are nonzero because their constant coefficients
  are one, and the dual block product is nonzero because it does not vanish
  at zero. `TemperedLFactorAlgebra.reflected_identity_of_quotient_ratio`
  turns the gamma ratio into the reflected identity between `D` and `E`.
- `reflectionRigidity` with radii `‖z 0‖⁻¹` and `‖z 0‖` applies. Their
  product is `1`, which exceeds the norm of the residue reflection scale by
  `TemperedLFactorAlgebra.norm_residueReflection_lt_one`. It gives `D = 1`,
  hence `P = ∏ i, (1 - C (z i) * X)`.

The published `eq_of_reflected_quotients` is not used. It requires
nonvanishing on the whole unit disk, which fails for non-tempered parameters.

**Induction.** `eq_prod_of_certificate` is by induction on the tuple length
`b + 1`. For `b = 0` the tail product is empty, so `eq_prod_of_tail_dvd`
applies directly. For a tuple of length `b + 2`, `exists_tail_dvd` gives a
tail certificate `Pt ∣ P`. The induction hypothesis on `Fin.tail z`, whose
absolute values are still weakly increasing, gives
`Pt = ∏ i : Fin (b + 1), (1 - C (z i.succ) * X)`. `eq_prod_of_tail_dvd`
concludes.

**Target.** `orderedUnramifiedPrincipalSeriesLPolynomial_of_rankOne`
rewrites the target's `eulerPolynomial (ofTuple z)` with
`Unramified.Eigenvalues.eulerPolynomial_ofTuple`. It then applies
`eq_prod_of_certificate` to the self-dual Haar measure `⟨ν, hν⟩`.

## Provenance

The route is the standard inductive computation of Rankin–Selberg
L-factors of induced representations: tail divisibility, followed by
comparison of the original and contragredient gamma factors. Jacquet,
Piatetski-Shapiro and Shalika, *Rankin–Selberg Convolutions* (1983),
registered as `jpss-1983-rankin-selberg`, use this route. The Lean proof
uses only the Library's closed theorems named above, and does not formalize
a particular page of that source. The ordering hypothesis is used only to
separate the root regions of the original and dual residuals.
