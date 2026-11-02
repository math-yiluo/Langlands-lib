# Finite composition series for products of supplied segment heads

Author: Worker 357.
Provenance: internal construction from published Library proofs.

`Langlands.PadicField.TopologicalData.SegmentProductDatum.compositionSeriesOfHeads`
chooses an actual finite composition series of the normalized product of
supplied segment heads. Its parameters are an arbitrary prime `p` with
`[Fact p.Prime]`, an actual `F : PadicField.{uF} p`, the supplied compatible
topological data `T`, a natural rank `n`, and
`d : T.SegmentProductDatum.{uV,uF} n`. Its only further premises are
`hd : d.HasSegmentHeads` and `hn : 0 < n`.

The returned data are

```lean
Σ m : ℕ, {s : ObjectRepFiltration d.induced.obj m // s.HasSimpleFactors}
```

Thus the result contains the length, a chain of actual invariant subspaces
from zero to the whole representation, and a proof that every successive
quotient is irreducible. The constructor makes a classical choice; it
asserts no canonicity, numerical length formula, or chosen identification
of its factors with segment representations.

The field universe `uF` and segment-base universe `uV` are independent.
The supplied heads and the induced carrier have universe `max uF uV`.
No resizing or equality of these universes is assumed. The product is
the existing actual upper block normalized induction, with its positive
half-modulus twist and right translation, using exactly `T`.
The construction preserves the ordered data and all repeated segments.

## Implemented construction and corollaries

`IsSegmentHead.isIrreducible` extracts irreducibility from the supplied
primitive strong-head relation. That relation already includes an actual
supercuspidal representative and a strong head of its increasing induction.
No theorem asserting existence of segment heads is used here.

`IsSegmentHead.isAdmissible` applies the published
`Langlands.CuspidalSupport.cuspidalEmbedding` to this irreducible head and
takes its admissibility conclusion. The underlying generic proof obtains
an embedding into induction of an irreducible quasicuspidal Levi
representation, proves that Levi representation admissible, applies
normalized induction admissibility, and transfers admissibility through
the injection. It also treats rank zero independently.

`SegmentProductDatum.HasSegmentHeads.isAdmissible` applies
`FiniteTensor.isAdmissible_external` to the actual head factors and then
`Parabolic.normalizedInductionAdmissibility` to their Levi tensor.
This corollary allows every total rank `n`, including zero.

`SegmentProductDatum.HasSegmentHeads.hasFiniteLength` specializes the
published `Langlands.Classification.irreducibleProductFiniteLength`
to `d.shape` and `d.blocks`, discharging each factor's irreducibility by
the first corollary. The generic theorem applies to arbitrary irreducible
smooth factors in positive total rank. Its carrier universe here is
instantiated at `max uF uV`; taking the maximum with `uF` again does not
change the induced carrier universe. Its conclusion is finite length over
the actual complex group algebra.

That generic proof embeds each irreducible factor into a cuspidal
induction, tensors the embeddings and induces them, then uses actual
ordered regrouping to identify the target with a flattened cuspidal
product. The latter has finite length by
`CuspidalSupport.cuspidalInductionLength`. Composing the first injection
with the inverse regrouping equivalence and applying
`IsFiniteLength.of_injective` gives finite length of the requested
product. The cuspidal length input uses the associated and nonassociated
geometric filtrations and a finite Jacquet detecting family; it does not
use a special-head Jacquet formula.

Finally, `MultiplicityAdditivityProof.exists_series` converts this
finite group-algebra length into an actual representation composition
series. It uses Mathlib's
`isFiniteLength_iff_exists_compositionSeries` and the published
`LengthCriterionProof.hasCompositionSeriesLength_of_compositionSeries`.
The latter carries the module chain through the order isomorphism between
group-algebra submodules and invariant subspaces. Covering steps become
irreducible actual quotient representations.
`compositionSeriesOfHeads` packages the resulting witnesses as a
nonempty dependent sum and applies `Classical.choice`.
It imposes no positivity condition on the chosen series length.

## Independence and scope

The direct imports are `Classification.LanglandsData`,
`Classification.IrreducibleProductFiniteLengthProof`, and
`Filtration.MultiplicityAdditivityProof`. All mathematical inputs are
reused by their published Lean names. This module is a derived choice and
specialization, rather than a translation of a new literature assertion.
The supplied-head relation, generic cuspidal embedding and finite-length
proofs, actual admissibility arguments, and the module-to-representation
series conversion supply its complete route.

An import inventory against published Library
`a5dff2ff93bd3637a67ee8847f67f811efc82f01` contains 496 project modules
including this new root and 183 external import roots. Every inherited
Lean/Markdown pair agrees byte for byte with that Library. There are no
derivative or mirabolic modules. A comment-free source scan finds no proof
holes or occurrence of the host's excluded target declarations. The
inherited classification modules are `ConstituentRelations`, `Essential`,
`IrreducibleProductEmbedding`, `IrreducibleProductEmbeddingStatement`,
`IrreducibleProductFiniteLengthProof`, `LanglandsData`,
`NormalizedProductFiniteLengthStatement`, `Segments`, `Supercuspidal`,
`SupercuspidalContragredientAux`, `SupercuspidalContragredientStatement`,
`SupercuspidalSupport`, `SupercuspidalTwist`, and `Tempered`.
The essential and tempered definitions in the closure provide no
classification conclusion to this construction.

The route uses no generic segment-product uniqueness, multisegment
exhaustion, ordered strong-head existence or conversion, quotient coverage,
tempered uniqueness, square-integrable classification or exhaustion, or
regular exhaustion. It uses neither segment derivative formulas nor
special-head or segment-socle Jacquet formulas, and no segment-socle
irreducibility or product-structure theorem. No parent irreducibility
criterion is assumed directly or transitively.

This supporting construction does not prove irreducibility of the
product or either direction of `SegmentHeadProductIrreducibility`.
The full criterion, including repeated segments and its independent
base universe, remains a separate proof obligation.
