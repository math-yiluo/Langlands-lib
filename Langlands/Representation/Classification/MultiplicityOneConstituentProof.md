# Multiplicity-one criteria for actual strong constituents

Authors: Workers 495 and 502. Worker 495 supplied the detector route; Worker 502 implemented
the actual product and constituent proofs.

`multiplicityOneConstituentCriterion` has exactly the proposition
`MultiplicityOneConstituentCriterionStatement` as its type. It pairs the
following two complete cores, importing the published target statement.

The reusable `Langlands.Classification.smoothProduct` constructs the actual
product of two smooth representations.
`Langlands.Classification.mappedProductSplitting` supplies the split image maps
used both here and by `PositiveTotalHeadCriterionProof`. Open subgroups fixing
each coordinate intersect to give an open subgroup fixing the pair. Under an additive functor, images of the four
actual inclusions and projections retain their identity and zero composites.
Thus the paired image projections are surjective, and the sum of the two image
inclusions is injective. These facts retain actual product carriers and do not
assume the two representations are inequivalent.

`multiplicityOneHeadCore` starts with the supplied actual smooth
irreducible quotient. Any competing algebraic irreducible quotient is smooth
by surjective smoothness transfer. If their kernels differ, the published
unequal-kernel theorem makes their paired map onto the actual smooth product
surjective. Epimorphism preservation makes its functor image surjective, and
the split image projections give a surjection onto the product of the two
functor images. The supplied positive series witnesses add by product
additivity; surjective monotonicity bounds their sum by one, a contradiction.
Hence all quotient kernels equal the chosen kernel, giving the existing strong
head relation in the original carrier universe.

`multiplicityOneSocleCore` starts with the supplied actual smooth irreducible
subrepresentation. A competing algebraic irreducible source is smooth by
injective smoothness transfer. Each actual image is an atom: restricting the
group-algebra linear map to its range gives a bijection, which transfers
simplicity from the irreducible source. Unequal atoms are disjoint. The sum of
the two embeddings on the actual product is therefore injective, including
when the two source representations are isomorphic. Monomorphism preservation
makes its functor image injective, and the split image inclusions inject the
product of the functor images into that image. Product additivity and injective
monotonicity again contradict the ambient count one. All irreducible embedding
images therefore equal the chosen image, which gives the existing strong
socle relation.

These are internal algebraic derivations using the existing constituent
relations, smoothness transfer, unequal-kernel product criterion and
Jordan–Hölder additivity and monotonicity. The private atom-image helper retains a local proof from the same algebraic
argument as the separately published extrema proof; no extra import is needed. No external theorem is
asserted as a source.

All five group, monoid and carrier universes remain independent. No
finite-dimensionality or local compactness premise is added. The assumed
series witnesses give exactly the finite-length information used in the
counting argument. Actual existence of a simple quotient or subrepresentation
and positivity of all detected simple objects remain hypotheses. No
unconditional segment existence, group-specific Jacquet assertion or
identification between the two strong constituents is claimed here.
