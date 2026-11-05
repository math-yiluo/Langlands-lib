# Splitness from pointed domination and finite primitive generators

Over a field k of prime characteristic p, let G be a smooth affine group scheme. Assume an actual pointed dominant morphism of relative schemes from a finite-rank split torus to G. Assume also a finite set T of primitive functions on the canonical affine coordinate corepresentation of G, and that the underlying functions in T generate its coordinate algebra over k. Then G is split unipotent over k.

The proof transports the pointed domination to the canonical corepresented affine model using its group-scheme isomorphism with G. Dominance forces this model to be connected. The existing smooth connected affine geometry theorem gives geometric integrality, hence reducedness. The pointed primitive polynomial-coordinate theorem then constructs an isomorphism from this model to a vector group over k. Composition with the canonical model isomorphism makes G a vector group. The existing finite additive series for a vector group gives the required represented split series.

`splitSeriesOfPointedFinitePrimitiveGenerators` chooses the length and the actual `HasSplitSeries` witness from this proof. The zero-dimensional vector group and a series of length zero are allowed.

The finite primitive generating set remains an explicit premise. This module does not derive it from commutativity or a prime-exponent condition, and does not assert the full all-characteristic domination statement. No homomorphism condition or boundary extension is imposed on the dominating morphism. The original ground field need not be perfect, algebraically closed or infinite.

The provenance is internal composition of `AffineCorepresented`, `PointedPrimitivePolynomialCoordinates`, `TorusSplitUnipotenceProof`, `SplitTorusDominationRefinement` and the vector-group split-series results in their import closure. The paired Lean uses these actual model, smoothness, reducedness, vector-isomorphism and split-series constructions.
