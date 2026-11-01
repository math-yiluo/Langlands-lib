# Proof of actual irreducible binary product commutation

Authors: Worker 78 and Worker 1023.

`Langlands.Classification.irreducibleBinaryProductCommutation` proves
`Langlands.Classification.IrreducibleBinaryProductCommutation.{uF,uV} F T`.
For positive, possibly unequal ranks `a` and `b`, and actual irreducible
smooth factors `α` and `β`, irreducibility of their upper normalized binary
product implies an actual isomorphism

```text
α × β ≅ generalLinearRankCast T (Nat.add_comm b a) (β × α).
```

The result retains the supplied compatible topological data `T`,
independent field and carrier universes, and factor carriers in
`max uF uV`. It assumes irreducibility of the original product; it neither
assumes irreducibility of the reversed product nor proves unconditional
binary irreducibility.

This is an internal derivation from lower published Library results. The
inverse-transpose pullback, Gelfand–Kazhdan topology adapter, normalized
product duality, product reversal, and product congruence helpers are
adapted from Worker 1023's published
`IrreducibleTwoFactorProductSwapProof`. Worker 78 extends that argument to
arbitrary reversed block shapes and identifies the exact unequal-rank
binary endpoint. The proof does not import the equal-rank theorem.

## Implemented proof

Write `θ` for `GeneralLinear.inverseTranspose`. The private abbreviation
`itPullback F T Z` pulls the action of `Z` back along `θ` on the same
carrier; continuity of inverse transpose preserves smoothness.
`itPullbackIso` pulls back an isomorphism with the same underlying linear
equivalence. `itPullbackTwiceIso` identifies the double pullback with the
original object through the identity map, using
`GeneralLinear.inverseTranspose_involutive`.

For positive rank `N`, `gelfandKazhdanEquiv` and `gelfandKazhdanIso`
identify the inverse-transpose pullback of an irreducible admissible object
with its smooth contragredient. They write `N = n + 1` to apply the
published `gelfandKazhdanContragredient`. Its canonical field topology is
transported to `T.topology` using
`T.topology_eq_canonicalNormTopology`; the group topology instance remains
an arbitrary argument during that transport.

Two further helpers supply the product comparisons:

- `itPullbackProductIso` bundles
  `Parabolic.normalizedProductInverseTranspose`: inverse transpose
  reverses the ordered block shape and pulls back each reversed factor.
- `productSmoothDualEquiv` identifies the smooth dual of a normalized
  product of admissible factors with the product of their smooth duals
  over the same upper parabolic. It combines
  `Parabolic.naturalNormalizedInductionDuality` with bijectivity of
  `FiniteTensor.smoothDualTensorMap`, using
  `FiniteTensor.smoothDualTensorInjectivity`,
  `FiniteTensor.smoothDualTensorMap_surjective`, and cofinal compact open
  subgroups of each block group. Admissibility of the external Levi tensor
  is `FiniteTensor.isAdmissible_external`.

The private theorem `irreducibleProductReverse` works for an arbitrary
positive total rank, block shape `B`, irreducible factors `A i`, and
irreducible original product `X`. Let `Y` be the product over `B.reverse`
of the factors `A i.rev`. The first conjunct of
`CuspidalSupport.cuspidalEmbedding` supplies admissibility of the factors
and of `X`.

Apply inverse-transpose product reversal to `Y`. Its shape becomes
`B.reverse.reverse = B`, and `Fin.rev_rev` restores each factor index.
Gelfand–Kazhdan on each factor, mapped through the normalized product
functor, then gives the product of their smooth duals. Product duality
identifies this with `X.contragredient`. Gelfand–Kazhdan on the irreducible
`X` identifies the same object with `itPullback F T X`. Hence
`itPullback F T Y ≅ itPullback F T X`. Pulling back that isomorphism once
more and using involutivity gives `X ≅ Y`. This uses no smooth
biduality and requires no irreducibility premise on `Y`.

For the public binary theorem, rewrite both binary functors with
`T.binaryNormalizedProductFunctor_of_pos`. Use
`B = BlockShape.binary a b ha hb` and
`C = BlockShape.binary b a hb ha`. The two entries of the first family
are irreducible by the supplied hypotheses, so
`irreducibleProductReverse` applies.

The private lemma `reverse_binary`, checked entry by entry on `Fin 2`,
shows

```text
C.rankCast (Nat.add_comm b a) = B.reverse.
```

The reversed family and the family `(β, α)` over that cast shape are
heterogeneously equal, also checked on `Fin 2`.
`productFunctor_obj_congr` transports this equality to a product
isomorphism. Finally `rankCastProductIso`, proved by substituting the
rank equality and taking the identity isomorphism, identifies the
product over the cast shape with the rank cast of the original product
over `C`. Composing these isomorphisms gives the literal endpoint required
by the statement.

## Dependency and independence audit

The direct mathematical inputs are Gelfand–Kazhdan, inverse-transpose
reversal of normalized products, natural normalized induction duality,
smooth duality of finite external tensors of admissible factors, and
admissibility of irreducible smooth representations from
`CuspidalSupport.cuspidalEmbedding`. The extra binary, rank-cast and block
equivalence imports identify the actual endpoint. No local binary
irreducibility criterion is used.

A recursive source audit of the complete project import closure at
Library base `676ac944440098acb714f6b953083e88bb89c9c2`, including this
proof and its authored proposition, resolved all 294 project modules.
There were no unresolved or unusual project imports and no occurrences
of the excluded statement modules or declarations in those Lean sources.
The only Classification modules are `ConstituentRelations`, this proof
and its statement, `Segments`, `Supercuspidal`,
`SupercuspidalContragredientAux`,
`SupercuspidalContragredientStatement`, `SupercuspidalSupport`, and
`SupercuspidalTwist`. Their role is definitions and lower transport facts,
rather than classification or exhaustion.

The excluded families checked were analytic segment classification
(task `aca8805b-054f-4d56-8045-12db7f623404`), multisegment special-head
exhaustion (`3bfb61fa-1129-4fc9-83fd-7fcfec22106e`), ordered strong-head
existence (`ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`), ordered quotient
coverage (`20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`), tempered-block
uniqueness (`52e97845-36bb-457d-b76f-70753334b88c`),
`SquareIntegrableLanglandsClassification`
(`1cb45da2-7007-4351-a694-594fb148b8d1`), square-integrable Langlands-head
exhaustion (`cd8ab97c-0b78-4bce-97c4-d307a28159a4`), and regular tempered
Langlands-head exhaustion (`bf433f0a-921a-428c-b0c0-6475438125ac`).
Their conclusions and proof successors cannot supply a proposition in
this closure through an imported statement. The implemented argument also
uses no global disjoint-support irreducibility, general ordered quotient
coverage, multisegment classification, or one-integral-line support
assertion under another name.

The `Derivative.Iteration` and `Induction.RankCast` imports provide the
entry-preserving total-rank cast used in the statement and final endpoint.
No derivative formula is invoked in this proof. No analytic
square-integrability criterion, actual Jacquet interchange, finite
grouping, or support-existence result is invoked.

Development compilation and theorem inspection succeed with zero errors
or warnings, reporting only `propext`, `Classical.choice`, and
`Quot.sound`. These checks do not establish independent semantic
acceptance or publication.
