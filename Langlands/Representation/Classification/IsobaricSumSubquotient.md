# Local isobaric sums in normalized block induction

`Langlands.PadicField.TopologicalData.IsIsobaricSum.isSubquotient_normalizedProduct`
starts with a positive total rank `n`, a `BlockShape n`, and smooth block
representations in the field and carrier universes of `IsIsobaricSum`. Any
supplied isobaric sum of the blocks is an actual subquotient of their normalized
upper-parabolic induction in the order of the given shape.

## Proof

Unpack the multisegment witnesses of `IsIsobaricSum` and induct on the length
of the block shape. An empty shape has rank zero. In a one-block shape the
block and total ranks agree. Transport the block to the total rank and use
`multisegmentHeadClassification` to identify it with the given head of the
same label. The actual one-block product evaluates to the transported block
by `singleBlockTransportedProductEquiv`.

For two or more blocks, `multisegmentHeadExistence` produces a head of the sum
of the tail labels. Its degree is the actual tail rank by additivity and
`degree_of_isLanglandsHead` for the input heads. The induction hypothesis puts
this head in the ordered tail product as a subquotient. The sum of all the
labels is the first block's label plus the sum of the tail labels. Apply
`langlandsHeadProductSubquotient` to these two labels, then
`binaryProduct_isSubquotient` to replace the tail head by the full tail product.
Compose the subquotient witnesses and apply `headTailBinaryProductIso` to
identify the binary product with the original block induction. Finally,
`SmoothRep.isSubquotient_iff_representation` converts the bundled occurrence
to `Correspondence.IsSubquotientOf`.

## Provenance

This is a finite-block consequence of the binary occurrence theorem, using
exactness and induction in stages for the original block order. It serves
the local occurrence step on the route to
`Langlands.Global.CuspidalIsobaricRealizationStatement`.

| Registered source | PDF SHA-256 | Locator and role |
| --- | --- | --- |
| `getz-hahn-2024-automorphic-representations` | `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507` | (10.33), p. 284 (PDF 296), defines the pooling of local Langlands data. Theorem 10.6.4, p. 286 (PDF 298), gives the local occurrence used in the proof of Theorem 10.7.5, p. 288 (PDF 300), under essentially unitary and generic hypotheses. |
| `tadic-1986-unitary` | `08e4e1e7c1ccc1e340999287867bc0448f3d8f4bab49906fbf1deda866ae4683` | Proposition A.4(ii), p. 372 (PDF 39), gives the binary occurrence for Langlands heads used at every induction step here. |
| `kudla-1994-local-langlands-nonarchimedean` | `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b` | Theorem 1.2.5(a)–(b), pp. 370–371 (PDF 380–381), describes the segment model of the Langlands classification used for head existence and comparison. |
| `zelevinsky-1980-induced-ii` | `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac` | §1.7, pp. 172–173 (PDF 9–10), gives associativity of the products by induction in stages. Lean uses the actual representation isomorphism for the original shape. |
