# Pointwise étaleness from a finite neighborhood family to every recognized piece

`Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.FinitePiecesEtaleAllPiecesStatement`
is a proposition about an actual strong map between the saturated presentations
of two affinoid atlases. At any source point, it asserts that
`HasFinitePiecesAt (fun _ _ f s => f.IsEtaleAtPoint s)` implies the corresponding
`HasAllPiecesAt` condition.

The hypothesis supplies open source and target neighborhoods on which the map
is finite, together with finitely many recognized target affinoid subsets. Each
contains the image point, their union is a neighborhood of that point, and every
recognized source piece realizing the prescribed inverse image has a finite
algebra map that is flat and unramified at the given spectrum point. The
conclusion supplies finite open neighborhoods on which this joint pointwise
condition holds for every recognized target affinoid subset containing the
image point. The conclusion need not use the same neighborhoods as the
hypothesis. Its quantification over source realizations and chart points is
exactly the one in `HasAllPiecesAt`.

The two pointwise conditions are carried on one finite family in the hypothesis.
The statement does not assert an implication for an arbitrary property of
bounded algebra maps, or that separate finite families for flatness and
unramifiedness have already been synchronized. It also does not assert that
pointwise étaleness holds on an open source neighborhood: that additional
quantifier belongs to `IsEtaleAtAllPieces`.

## Provenance and scope

This is a derived prerequisite for strong étale right cancellation, formulated
in the Library's full-recognition language. Its flatness input is Berkovich,
*Étale cohomology for non-Archimedean analytic spaces* (1993), Proposition
3.2.3(a) implies (b), printed pages 58–59 (retained PDF pages 55–56). That proof
uses the finite affinoid covering criterion, Lemma 3.2.4 on printed page 59.
The unramifiedness input is locality of the vanishing of the relative
differential module, compared with Proposition 3.3.7(b), printed page 63
(PDF page 60); Proposition 3.3.3(i), printed pages 62–63 (PDF pages 59–60),
gives the differential module's compatibility with base change. The combined
statement is not a verbatim theorem of the source: a proof must realize these
operations for the actual recognized pieces and their pullback algebra maps.

The field, space and atlas-index universes are independent. The statement
assumes only a complete ultrametric normed ground field, allowing trivial
valuation and arbitrary positive finite polyradii. There is no Hausdorff
assumption on the ambient analytic spaces. It supplies neither a proof of the
finite-cover criterion nor a proof of strong right cancellation; these remain
separate obligations. The imported target statements and their imports are
unchanged.
