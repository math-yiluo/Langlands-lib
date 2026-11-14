# Conditional finite subcovers in the analytic étale site

Author: Worker 284.

This is an internal derived construction from the published analytic étale site,
the twisted topology, and Mathlib's compact finite-subcover theorem. It does not
assert the unresolved geometric hypotheses.

`exists_finite_etale_subcover` takes a sieve on an object with compact underlying
space, open underlying maps for arrows to that object, and joint surjectivity
of the arrows in the sieve. It chooses an arrow above each point, takes a finite
subcover of their open ranges, and reindexes that finite family by `Fin n`. Joint
surjectivity places the finite family in the existing étale precoverage, hence
its generated sieve covers. No prior covering assumption on the original sieve
is needed beyond the explicitly supplied point-surjectivity.

`exists_finite_twistedEtale_base_subcover` applies this construction to the
ordinary arrows of a twisted covering sieve on the base object. A map over `X`
to the identity object has underlying arrow equal to its source structure map,
so the stated structure-map openness hypothesis suffices. The twisted topology
definition makes the ordinary sieve covering. The point-surjectivity hypothesis
then supplies its point cover. Finally, the published cover-preserving property
of the ordinary-to-twisted inclusion makes the finite family a twisted cover.
The resulting family lies in the original twisted sieve.

`finiteTwistedEtaleBaseSubcover` selects such a family by classical choice. Its
value consists of a natural number `n`, objects indexed by `Fin n`, and arrows
to the twisted base, with proofs that every arrow belongs to the original sieve
and that the family generates a covering sieve. It has precisely the same
compactness, openness, point-surjectivity, and covering assumptions as the
existence theorem.

The second result retains compact Hausdorff `IsCompactSpace X`, though its proof
uses only compactness. It assumes openness of all étale structure maps and
point-surjectivity of ordinary covering sieves. Neither is proved here, and this
module supplies no unconditional cohomological comparison or smoothness theorem.
