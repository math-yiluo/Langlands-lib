# Analytic Galois covers on the ordinary étale site

Suppose an arrow between two étale objects over the same analytic space
has an analytic Galois cover given by deck graphs.
`AnalyticGaloisCover.toEtaleSiteCover` makes the arrow a Galois covering
for the ordinary étale topology. Pointwise surjectivity gives the
covering sieve. Two arrows with the same composite to its base agree
locally up to a deck transformation because each deck graph is open.
Freeness on arrows from nonempty spaces follows from disjointness of
the graphs. The empty sieve covers a space with no points.

For a finite deck group the analytic cover is proper on underlying
spaces. It is an open quotient map since it is étale and surjective.
The preimage of the image of a closed set is the union of its finitely
many deck translates, hence closed. The fibres are finite orbits and
therefore compact.

The graph of any arrow between two étale objects over the same space
is a section of an étale pullback projection and therefore an open
immersion. The other projection is étale as well. Their composite
gives étaleness of the original arrow.

This internal construction connects the Library's analytic deck-graph
definition to the categorical Galois covering used for descent and
group cohomology. Properness lets a finite family of local restrictions
cover an entire fibre after shrinking the base.
