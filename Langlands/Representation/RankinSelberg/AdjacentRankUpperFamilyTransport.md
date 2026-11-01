# Actual adjacent upper-family and certificate transport

Worker 486. This internal composition proves an actual normalized induction
comparison and complete certificate transports for the adjacent analytic
base. The field and the two original carrier universes remain independent.
Every natural rank, including zero, and reducible full Whittaker-type blocks
are retained. It is a transport contribution, not either closed parent proof.

`AdjacentRankUpperFamilyComparison F r h sigma` records a continuous scalar
quasicharacter, an equivalence from the original first block to its exact
lifted scalar action, and an equivalence from the actual original upper
induction to the actual normalized lower induction of the original second
block and that lifted scalar action. Its original upper predecessor sizes
are `(0,r)`, so the actual upper ranks are `(1,r+1)` and the total rank is
`r+2`. The lower ranks are `(r+1,1)`.

## Constructing the complete family comparison

`normalizedProductInducedEquiv_of_sizes` is a dependent size adapter. A
pointwise size equality identifies the source shape with the successor
shape of the given predecessor sizes. Representation equivalences between
the corresponding blocks, including their original module instances,
then induce an equivalence of the actual normalized upper inductions by
`TopologicalData.normalizedProductInducedEquiv`. Its proof eliminates the
shape constructor and the equality of size functions, so the positive
half-modulus and ordered tensor actions are the same. No intertwiner or
induction equivalence is an extra premise of the main comparison theorem.

`adjacentRankUpper_exists_lowerCharacterEquiv` proves the comparison from
full standard-character Whittaker type of the original blocks. The published
`rankOneCharacterReduction` gives an actual representation equivalence
from the arbitrary original rank-one carrier to the scalar action of a
continuous quasicharacter. The linear equivalence to `ULift C` then gives
exactly `rankOneExtensionCharacter`, whose full type and smoothness are
already published. The original second block is retained on its original
carrier.

The published `glOppositeProductReversal` maps lower blocks `(r+1,1)`
to upper blocks `(1,r+1)`. This is the actual normalized parabolic
comparison, with the complete ordered dependent family reversed: sizes,
carriers, module instances and representations. Its reversed first block
is the lifted scalar action, which is carried back to the original first
block using the rank-one equivalence. Its reversed second block is the
original second representation. Applying the size adapter and composing
with the inverse reversal produces the claimed induction equivalence.
It does not infer an induction comparison merely from commutativity of a
product of factors. The rank-equality cast fixes the carrier in its motive,
so it does not alter the dependent carrier instances.

## Complete certificates for the parent's arbitrary family

`adjacentRankUpperL_of_lowerCharacter` and
`adjacentRankUpperGamma_of_lowerCharacter` start with the parent's arbitrary
`t`, size function `m`, sum proof and dependent original block family.
The actual hypotheses `t=r+1` and `m 0=0` imply `m 1=r`. Replacing the size
function by `(0,r)` transports the whole original telescope. The preceding
comparison chooses the quasicharacter and both actual equivalences.

Each consumer has an explicit `hLower` input: for every original first lower
carrier and every quasicharacter, it supplies the corresponding complete
lower-induction and original block certificates. The input requires the
original first lower block's full type. It does not require irreducibility,
an ambient type, or a comparison equivalence. No claim is made here that
this arbitrary-character analytic input has been proved.

The published `IsPadicSymmetricLPolynomial.congr_equiv` or
`IsPadicSymmetricGammaFactor.congr_equiv` carries the full ambient certificate
through the actual induction equivalence and the full scalar certificate
through the original rank-one equivalence. The test representation, additive
character and supplied additive Haar measure stay the same. These are the
complete symmetric relations, including their compatible-measure existence
witnesses, universal measure and functional quantifiers, all applicable
blocks and functional-equation clauses. A certificate is not replaced by
an equality between chosen scalar labels.

The block family of polynomials or gamma factors in the original upper order
is `(P1,P0)` or `(G1,G0)`. After the actual representation comparison has
been constructed, product commutativity identifies its finite product with
the lower-order product. The L consumer retains exactly

```text
exists Q e, X^e * (product_i Pi i) = Q * P.
```

The gamma consumer retains certification of exactly `product_i G i` for
the actual upper induction.

## Provenance and remaining scope

This is internal composition of the named published rank-one reduction,
normalized reversal, block-equivalence and certificate-equivalence APIs.
It asserts no new literal source theorem and uses no later unrestricted
multiplicativity or rank descent. Existing Library pairs are unchanged.
The complete lower `hLower` inputs assert arbitrary-character analytic
results. The current sufficiently-large-second-twist theorem does not
supply them, since its strict real bound cannot be discarded. Parameter
specialization, the necessary functional equations and both unchanged
closed adjacent-rank parent proof records remain separate obligations.
