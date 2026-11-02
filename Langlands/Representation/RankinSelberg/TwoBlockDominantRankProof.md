# The dominant-rank gamma and L analytic bases

`Langlands.RankinSelberg.twoBlockLDominantRank` proves exactly the existing
`TwoBlockLDominantRankStatement.{uF,uV,uW}`, and
`Langlands.RankinSelberg.twoBlockGammaDominantRank` proves exactly the existing
`TwoBlockGammaDominantRankStatement.{uF,uV,uW}`, both from
`TwoBlockBaseCasesStatement`. The field, test carrier and dependent block
carriers have independent universes. The sole added rank restriction is
`t ≤ r`, including equality. Every character and supplied self-dual Haar
measure in the statement is retained. The test and two block representations
have full Whittaker type, including reducible representations. No induced
type, irreducibility, factor-existence or analytic identity is added as a
premise.

Both conclusions concern the actual canonical normalized upper product
`F.canonicalNormalizedProductInduced (succBlockShape m h) sigma`. The L conclusion supplies
its complete symmetric L-polynomial certificate, complete symmetric
certificates for both original blocks, and ordinary polynomials `Q` and a
natural exponent `e` satisfying exactly
`X ^ e * (∏ i, Pi i) = Q * P`.

## Lower analytic conclusion

`lowerLDominant` discharges the previously conditional
`DominantRankTransport.LowerLDominantInput` with its full original telescope.
It first proves the lower two-block symmetric L bound, splitting `t ≤ r`
into `t < r` and `t = r`.

In strict rank, `strictTwoBlockSymmetricLBound_at_zero` from the companion
`TwoBlockDominantStrictLContinuation` module supplies the bound. That module
uses genuine unequal-rank analytic expansion, retained first-block certificates
on a real opposite-twist ray, complete unramified L-polynomial transport,
entire actual determinant-slice families and specialization to zero. The
closed first-block analytic premise of
`exists_strictTwoBlockSymmetricLBound` is discharged by the independently
published exact theorem `twoBlockDominantFirstBlockLaurentIdentity`; no
unproved proposition is supplied as evidence. The companion Markdown details
the actual coefficient and intrinsic-generator argument.

At equality, the proof transports the rank equality and applies the published
`equalTwoBlockSymmetricLBound_at_zero`. That theorem supplies the actual lower
induction bound using the equal-rank integral, entire determinant slices and
the same opposite-twist specialization route.

Both branches return the same three complete symmetric L certificates and
`X^e * (P0 * P1) = Q * P`. The proof packages the two polynomials as the actual
`Fin 2` family `![P0,P1]`; finite case analysis proves both block certificates,
and the two-element product formula gives the exact requested equation.
The induced Whittaker type and factor existence used inside these branches
are proved from the supplied block/test type hypotheses by the imported
normalized-induction and symmetric-factor-existence theorems.

## Lower gamma conclusion

`lowerGammaDominant` discharges the full conditional
`DominantRankTransport.LowerGammaDominantInput`. It splits precisely `t ≤ r`
into strict rank and equality. The strict branch applies
`strictTwoBlockSymmetricGammaProduct_at_zero` from
`TwoBlockDominantStrictGammaContinuation`; equality applies the published
`equalTwoBlockSymmetricGammaProduct_at_zero` after rank transport.

The strict continuation preserves the actual dual integral's right Weyl
translation, swaps its complementary rows, and absorbs the model sign by the
fixed central translation `(-1)^r`. Both literal coefficient families are
entire and both actual integrals have absolute spectral expansions. The
complete real-ray gamma equation, combined with the L clearing kernel, is
continued to zero and the original model sign is restored. A nonzero actual
integral retained in a complete induced gamma certificate identifies that
certified factor with the product of the two certified original block factors.
The first-block analytic premise is discharged by the same published exact
first-block theorem used for the L argument. The companion Markdown explains
the implemented actual-family continuation in detail.

The proof packages the returned two rational factors as `![G0,G1]`; case
analysis retains both complete block certificates and the two-element product
formula retains the complete induced-pair certificate.

## Actual normalized lower-to-upper transport

The exact target theorems apply the published `lDominant_of_lower` and
`gammaDominant_of_lower` to the respective proved lower inputs. That transport evaluates the lower theorem on the complete
reversed family: block sizes `m i.rev`, carriers `W i.rev` and representations
`sigma i.rev`, with their transported additive and module structures and
reindexed rank sum.

`lowerReversedToUpperEquiv` applies the actual normalized opposite-product
reversal theorem `glOppositeProductReversal` to that reversed lower induction.
The second reversal recovers the original upper block family, identified as a
whole dependent family. The resulting representation equivalence includes the
actual normalized induction and right translation actions. The complete
symmetric L and gamma certificates are transported along it by
`IsPadicSymmetricLPolynomial.congr_equiv` and
`IsPadicSymmetricGammaFactor.congr_equiv`, respectively.

The block polynomials and rational gamma factors are reindexed back by `Fin.revPerm`. The finite product
is invariant under this reindexing, and the original `Q` and `e` are preserved.
Product commutativity is not used to identify induced representations.
All compatible-measure and normalized-generator quantifiers and the existence
witnesses in the complete certificates remain inside the unchanged predicates.

## Source route and scope

This is an internal assembly of the independently developed Section 4 analytic
and representation-transport results. The registered source context is
Jacquet–Piatetski-Shapiro–Shalika, *Rankin–Selberg Convolutions* (1983), Theorem
3.1(i)–(ii), printed pages 404–405; Section 4, pages 406–420; and the dominant base
in Section 7.1(1), pages 438–439. The source's Laurent inclusion corresponds
to the displayed equation in precisely this direction. The registered source
and errata checks are retained in the task's reading record; no applicable
registered JPSS erratum was found.

Neither unrestricted two-block multiplicativity, finite-block
multiplicativity nor later Section 7 rank descent is used. The target pair
and its imports are unchanged. The Lean module supplies both exact targets. The two separate proof records
name their respective existing statements and require their own exact-target
validation, independent semantic acceptance and publication.
