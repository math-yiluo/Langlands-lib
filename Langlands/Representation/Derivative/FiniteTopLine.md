# Scalar top derivatives of finite ordered products

`Langlands.Derivative.finiteProductTopDerivativeLineEquiv` constructs a complex
linear equivalence from the entire top derivative of an actual finite ordered
normalized product to the complex scalars. Its inputs are an ordered positive
block shape `B` of positive total rank `n`, smooth complex factors `σ i` on the
actual block groups, and a complex linear equivalence from the entire
order-`B.size i` derivative of each factor to the scalars.

The parameters include arbitrary `p` with `Fact p.Prime`, a p-adic field `F`
in universe `uF`, supplied topological data `T`, and a bundled continuous
nontrivial unitary additive character for that topology. The universe parameters
`uF` and `uV` are independent. Each input factor has carrier universe
`max uF uV`; the normalized product and its derivative have that same universe.
This is a constructor for factors already in this carrier universe. It makes
no comparison with the derivative of an arbitrary factor in the smaller
universe `uV`.

The source is literally the carrier of
`generalLinearDerivative T ψ n n le_rfl` applied to
`(T.normalizedProductInductionFunctor B).obj σ`. The output is linear data
on this whole carrier, including an inverse. The target is the full scalar
space `ℂ`. No finite-dimensionality, admissibility, irreducibility, finite
length, unitarity, or additional regrouping hypothesis is assumed. The given
factor equivalences are the explicit nonvanishing and dimension-one input.
All ranks of individual blocks are positive by `BlockShape`; total rank zero
is outside the construction.

The implementation first provides four elementary adapters.

1. `topMapEquiv` maps a categorical isomorphism between representations in the
   same carrier universe through the actual top-derivative functor and takes
   its underlying linear equivalence.
2. `topTransportLine` transports a scalar equivalence along equality of ambient
   ranks. Equality elimination proves it; no change of normalization occurs.
3. `binaryTopLine` identifies the direct two-factor family with
   `binaryPairFamilyFunctor` by its two coordinates, maps this equality through
   normalized induction, and uses `binaryNormalizedProductPositiveIso` to reach
   the all-rank binary product. It then composes `topProductTensorEquiv`,
   `TensorProduct.congr` of the two supplied scalar equivalences, and the
   tensor left-unit equivalence `ℂ ⊗[ℂ] ℂ ≃ₗ[ℂ] ℂ`.
4. `singleFamily_eq` identifies an arbitrary one-block family with the canonical
   family transported from its unique factor. After identifying the indices,
   the two opposite equality transports cancel.

`singletonTopLine` uses the last identification under the normalized-product
functor, followed by `singleBlockTransportedProductEquiv`, to identify the
product with its unique factor transported to total rank `n`. Mapping this
isomorphism through the derivative and composing with `topTransportLine`
gives the singleton scalar equivalence.

The private existence proof uses strong induction on `B.length`. An empty
family has total rank zero by `B.sum_eq`, contradicting positive total rank.
The one-block case is the preceding singleton construction. With at least two
blocks, `headTailProductInductionIso` identifies the product with the actual
two-block product of its first factor and its ordered nonempty tail. The first
factor has the carrier lift appearing in that published isomorphism.
`SmoothRep.universeLiftEquiv` removes this lift by an actual representation
equivalence. Both its carriers are in `max uF uV`, so this equivalence gives
a categorical isomorphism in the same category and can be mapped through the
top derivative. The supplied scalar equivalence then handles the first factor.
The tail has fewer blocks and positive rank, so induction supplies its scalar
equivalence. The head/tail outer shape is the rank-transported binary shape;
coordinatewise equality identifies its factor family with the direct binary
family. Mapping the split through the top derivative and composing with
`binaryTopLine` finishes the induction.

The public definition selects the resulting linear equivalence by classical
choice. No preferred basis, evaluation formula, or naturality in the supplied
factor equivalences is asserted. The construction preserves the original
ordered labels, including repeated factors; no permutation argument is used.

The provenance is derived composition of the existing general
`topProductTensorEquiv`, ordered first/tail induction, singleton evaluation,
equality transport, carrier lifts, and elementary tensor equivalences.
The binary comparison in turn uses the proved general derivative Leibniz
filtration. This unit introduces no additional literature assertion or
individual segment derivative formula.

The import audit against Library
`dac2bb9e83346876770fced17af26f0cba7f4c98` records 395 project modules including
this new module and 143 external import roots. Of these, 392 inherited
Lean/Markdown pairs match that Library exactly. The remaining two prerequisite
modules, `Derivative.TopProduct` and `Filtration.SingletonIso`, match the frozen
bytes of their separately reviewed supporting construction. The closure is
the union of that general binary-comparison closure and the previously
inspected published `HeadTailProductInduction` closure, with this module added.
The audit has no missing module, unpaired Lean file, proof hole, or
excluded-conclusion name hit.

The only inherited classification modules are `Supercuspidal`,
`SupercuspidalContragredientAux`, `SupercuspidalContragredientStatement`, and
`SupercuspidalTwist`; they provide general predicate, duality, lift, and twist
infrastructure. No prohibited classification or exhaustion conclusion,
partial-Jacquet consumer, Zelevinsky 1980 segment derivative formula, or
segment-socle assertion is imported. This is an import and byte audit combined
with the existing prerequisite audits, not a claim to have reread every
inherited module body.

This supporting constructor leaves individual special-head top-derivative
nonvanishing and both directions of `SegmentHeadProductIrreducibility` open.
Its explicit factor-equivalence inputs must be established separately before
applying it to those products.
