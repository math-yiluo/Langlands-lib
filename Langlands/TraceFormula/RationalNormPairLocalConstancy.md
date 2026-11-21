# Rational approximation with a locally constant comparison

`rationalNormPairLocalConstancy` proves
`RationalNormPairLocalConstancyStatement`. Let \(L/K\) be a cyclic extension
of number fields with a chosen generator. At each place in a finite
family of finite places of \(K\), take a regular associated pair of
matrices in the completed tensor algebra and base completion, and a
neighbourhood of each matrix. At a distinguished place of the family,
homeomorphic ring isomorphisms identify the local scalar inclusion
and cyclic action with those of a cyclic algebra over a characteristic-zero
nonarchimedean local field. The target algebra has its module topology.

Let \(P(\delta,\gamma)\) be a proposition on the two target matrix groups
whose truth value is locally constant on the subtype of regular associated
pairs. There is one rational associated pair, with regular semisimple
base matrix, whose localizations lie in all the prescribed neighbourhoods.
Under the distinguished coefficient isomorphisms it has the same
truth value of \(P\) as the chosen local pair.

The proof chooses a neighbourhood of constancy in the subtype and
lifts it to an open set in the product of matrix groups. It shrinks
the two distinguished neighbourhoods using a product neighbourhood
inside that open set and the openness of regular norms. Simultaneous
rational norm approximation gives a pair in all the refined
neighbourhoods. Norm association localizes and is preserved by the
coefficient isomorphisms. Separability of the characteristic polynomial
descends from the base completion to \(K\).

This internal lemma separates the approximation step in
Henniart–Lemaire, I.6.8 (printed pp. 49–50), from the analytic local
constancy assertion used there. It applies to `ConcordAt` once its
local constancy for the fixed tests and ambient Haar measures is supplied.
