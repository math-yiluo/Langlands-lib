# Binary reduction for Bernstein's unitary product theorem

Author: Worker 103.

This internal reduction isolates the positive-rank binary irreducibility input
needed by `Langlands.Classification.BernsteinUnitaryProductIrreducibility`.
It does not prove the binary input or the final theorem unconditionally.
The field universe `uF` and representation universe `uV` are independent;
all block carriers lie in `Type (max uF uV)` and the supplied topology is used.

`BernsteinPositiveBinaryUnitaryProductIrreducibility F T` is a Prop-valued
definition. It states that the literal normalized binary product of two
irreducible unitarizable smooth representations of positive ranks is
irreducible. The product's unitarizability is supplied by the published
`glNormalizedProductInductionUnitarity`, so it is not a premise of this
binary statement.

`bernstein_emptyProduct_irreducible_unitarizable` proves that the actual product
on every shape of total rank zero is irreducible and unitarizable. The published
`emptyProductUnitIso` identifies that product with the trivial representation
on `ULift ℂ`. Its carrier has dimension one. The subrepresentation lattice
embeds in the simple submodule lattice of that carrier, giving irreducibility.
The usual positive form on `ℂ` pulls back through `ULift.moduleEquiv` and the
actual product isomorphism to give an invariant positive form.

`bernstein_product_unitarizable` extends the published positive-rank preservation
theorem to every total rank, using this empty-product case at rank zero.

`bernsteinUnitaryProductIrreducibility_of_binary` inducts on the number of
blocks. With zero blocks the sum of the sizes forces total rank zero. With one
block, evaluation in `singleBlockNormalizedProductEquiv` identifies the product
with its one factor pulled back along the explicit equality of ranks; the
reindexing is the identity after eliminating that equality. With two or more
blocks, `headTailBinaryProductIso` identifies the product with the binary
product of its original head and its actual ordered tail, followed by the
published equality transport of the ambient rank. The induction hypothesis
gives irreducibility of the tail, and preservation gives its unitarizability.
The supplied binary assertion therefore applies. Irreducibility transports
back through the actual isomorphism. The final pair uses the all-rank
unitarizability lemma.

The provenance is an internal composition of published tensor, induction,
regrouping, rank-transport and positive-form results. No new external assertion
is translated. Bernstein 1984, Corollary 8.2(a), and Tadic 1986, Theorem 2.5(i),
state the binary theorem; the fixed Library target is its finite-family form.
This module supplies the finite-family reduction recorded as an obligation in
`BernsteinUnitaryStatement.md`. It uses neither central exponents nor derivative
positivity nor a classification theorem as an additional hypothesis. The only
remaining premise of the final reduction is the displayed positive-rank binary
assertion.
