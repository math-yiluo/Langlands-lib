# From pair-factor orders to generated integral descent

This module proves
`Langlands.Global.PoleComparison.PolePairingDescentStatement`
as the theorem `Langlands.Global.PoleComparison.polePairingDescent`.
The proof is universal in all five types: the source basis `ι`, the target
basis `κ`, the generator index `J`, and the two omitted-place types `A` and
`B`, each in its own universe. The theorem is the pair of its two
components, `poleGramComparison` and `poleGeneratedDescent`.

## Pole orders give Gram equality

`poleGramComparison` proves `PoleGramComparisonStatement`. Fix generators
`j` and `k`. The hypothesis `RegularPairComparisonsAt d 0` supplies, for
this pair, meromorphy of the two pair factors, the omitted-unit and
boundary-unit conditions on both sides, and equality of the completed
punctured germs at `0`. These are exactly the hypotheses of the published
finite-unit order-transfer theorem
`Langlands.Global.PoleComparison.completedPoleTransfer`, which is applied
at `z = 0` to `d.left j k` and `d.right j k`. It gives equality of their
meromorphic orders at `0`.

The two `RealizesPairingAtZero` hypotheses rewrite these orders as the
images in `WithTop ℤ` of `-pairing (left j) (left k)` and
`-pairing (right j) (right k)`. Injectivity of the embedding of `ℤ` into
`WithTop ℤ` (`WithTop.coe_inj`) and of negation (`neg_injective`) then
gives the exact integer equality
`pairing (left j) (left k) = pairing (right j) (right k)`.

## Gram and degree equality give the generated isometry

The auxiliary theorem `generatedPositiveIsometry_of_gram` assumes equal
generator pairings and, for every `j`, equality of the target degree of
`right j` with the source degree of `left j`. It reuses the published
results of `Langlands.VirtualRepresentation.DescentProof`:

- `integralRelationDescent` gives `relations left = relations right`.
- `integralGeneratedEquivalence` then gives a unique linear equivalence
  `T` between the generated spans that sends each generator image of
  `left` to the corresponding generator image of `right`.
- `integralGeneratedIsometry` and `integralGeneratedDegree`, applied to
  the underlying linear map of `T`, show that `T` preserves pairings and
  degrees.
- For the last clause of `GeneratedPositiveIsometry`, let `x` have
  pairing `1` with itself and positive source degree. Preservation of
  pairings and degrees shows that `T x` has self-pairing `1` and positive
  target degree, so `integralPositiveDegreeBasis` for `κ` and the target
  weight gives a unique `i` with `T x = generator i`.

Every equivalence satisfying `GeneratedPositiveIsometry` satisfies its
first clause, the generator-image condition. The uniqueness part of
`integralGeneratedEquivalence` therefore identifies it with `T`, which
proves uniqueness.

## The generated descent statement

`poleGeneratedDescent` proves `PoleGeneratedDescentStatement`. It applies
`generatedPositiveIsometry_of_gram`. Gram equality comes from
`poleGramComparison`. The degree hypothesis comes from the two rank
formulas: the target degree of `right j` and the source degree of
`left j` both equal the integer `rank j`. The proof uses only this common
value; the positivity of `rank j` is not used.

## Provenance and scope

The Lean proof was written by Worker 64 in the shared H1 draft of task
`205503d3-82c7-4b1a-a4f0-90d02bbe9a2e` and is reused here unchanged. It
implements the derived generic pole-to-pairing argument of Henniart
(2000), §§2.5–2.8, printed pp.445–448. That source compares poles of
pair factors to obtain equality of pairings and then descends integral
relations. The generic formulation is internal, as explained in the
statement's Markdown.

All analytic and representation-theoretic inputs remain hypotheses of the
statement: meromorphy, the omitted and boundary units, the completed-germ
comparisons, and the signed pole formulas. The result is an equivalence
of generated integral spans only. It proves neither ambient spanning nor
surjectivity on basis indices. It also proves no local pole formula, no
global functional equation and no global boundary nonvanishing.
