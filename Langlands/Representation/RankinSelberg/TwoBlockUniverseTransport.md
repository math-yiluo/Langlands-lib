# Carrier-universe transport for two-block pair factors

Author: Worker 592.

This internal module derives carrier transport from the published Library
definitions and actual representation equivalences. It makes no new analytic
or original literature claim. In particular, each closed reduction assumes the
corresponding full two-block multiplicativity statement in a common universe;
neither factor existence nor multiplicativity is proved without that premise.
The imported statement definitions and their source pairs are unchanged.

`Langlands.PadicField.TopologicalData.normalizedProductInducedUniverseLiftEquiv`
takes any supplied p-adic topological realization `T`, any ordered block shape
`B`, and an entire dependent family of actual block representations `σ i` on
`V i : Type uV`. It returns an actual representation equivalence from
`T.normalizedProductInduced B σ` to the normalized induction of
`fun i => Langlands.universeLiftRepresentation.{uX} (σ i)`.
It applies the published `T.normalizedProductInducedEquiv` to the full family
`fun i => Langlands.universeLiftEquiv.{uX} (σ i)`. Thus its forward map applies
the induced tensor of the forward carrier lifts to each function value, and
its inverse uses the corresponding inverse maps. The published construction
supplies equivariance and both inverse identities. It preserves the complete
ordered shape, block sizes, ambient group, positive half-modulus character,
and normalized upper induction. No product identity or assumed comparison is
used. Empty shapes are allowed by the underlying API. The field, original
carrier and lift universes are independent; the induced carriers have
universes `max uF uV` and `max uF uV uX`.

The general carrier lift and its equivalence are imported from
`Langlands.Representation.Category.UniverseLift`, without reconstructing them.
`RankinSelberg.isOfWhittakerType_universeLift_iff` specializes the published
`isOfWhittakerType_iff_of_equiv` to that actual equivalence. It preserves all
three clauses: admissibility, finite generation over the group algebra, and
an equivalence from the entire Whittaker functional space to the scalars.
It keeps the same unipotent character and applies over any topological field.
No irreducibility or selected functional is assumed.

`RankinSelberg.isPadicSymmetricGammaFactor_universeLift_iff` and
`RankinSelberg.isPadicSymmetricLPolynomial_universeLift_iff` specialize the
published symmetric `congr_equiv` laws. The two original carrier universes
and the two lift universes are independent. They preserve the given field,
character, Haar measure and rational-function or polynomial witness. They
apply in both rank orders, retaining the existing equal-rank convention;
they do not exchange the representations. The measure can be any supplied
additive Haar measure, so these helpers also apply to the self-dual Haar
data in the two-block statements.

`RankinSelberg.twoBlockGammaMultiplicativity_of_commonUniverse` has the closed
type

```text
TwoBlockGammaMultiplicativityStatement.{uF, max uF uV uW, max uF uV uW} →
  TwoBlockGammaMultiplicativityStatement.{uF, uV, uW}.
```

Its proof introduces the entire original telescope and lifts the first
representation and every block representation by `U = max uF uV uW`.
All lifted carriers lie in `Type U`. It transports the full Whittaker-type
hypotheses and applies the supplied common-universe statement. It keeps the
resulting finite family `G : Fin 2 → RationalFunctions` and its product
unchanged. Each block certificate returns through the actual carrier
equivalences. The induced certificate returns through the first carrier
equivalence and `normalizedProductInducedUniverseLiftEquiv` at
`T = F.canonicalTopologicalData`, `B = succBlockShape m h`. The conclusion is
therefore the certificate for the original
`F.canonicalNormalizedProductInduced (succBlockShape m h) σ`.

`RankinSelberg.twoBlockLFactorMultiplicativity_of_commonUniverse` has the
parallel closed type

```text
TwoBlockLFactorMultiplicativityStatement.{uF, max uF uV uW, max uF uV uW} →
  TwoBlockLFactorMultiplicativityStatement.{uF, uV, uW}.
```

It uses the same full telescope, lifts, type transport and actual induced
equivalence. It returns the original induced and block carriers with the
same certified `P : ℂ[X]` and `Pi : Fin 2 → ℂ[X]`. It passes through the
entire divisibility witness, including `Q : ℂ[X]`, `e : ℕ`, and the exact
equation `X ^ e * ∏ i, Pi i = Q * P`, without changing its direction.

Both reductions retain every prime, p-adic field, canonical topology,
unitary additive character, supplied self-dual Haar measure, rank, positive
block shape and dependent block carrier family in the original statements.
Reducible representations remain allowed. There is no new assumption about
induced Whittaker type, analytic factors, rank order, smallness, carrier
dimension, or universe inequality. Stability under further normalized
induction comes from `max uF U = U`; performing the analytic descent in that
stable universe is a separate obligation.

All new helpers and reductions are in this single Lean/Markdown pair. The
published source pairs reused unchanged are
`Langlands/Representation/Category/UniverseLift.{lean,md}`,
`Langlands/Representation/Induction/BlockEquivalence.{lean,md}`,
`Langlands/Representation/RankinSelberg/WhittakerTypeEquivalence.{lean,md}`,
`Langlands/Representation/RankinSelberg/PadicPairFactors.{lean,md}`, and
`Langlands/Representation/RankinSelberg/TwoBlockMultiplicativityStatement.{lean,md}`.
Their existing imports supply the underlying induction and factor definitions.

The module compiled without errors or warnings in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. Inspection of the new actual induced
equivalence reports precisely the independent universe parameters `uF, uV, uX`;
each closed reduction reports `uF, uV, uW`. Their inspected assumptions are
only `propext`, `Classical.choice`, and `Quot.sound`. These development checks
do not supply independent semantic acceptance or Library publication.
