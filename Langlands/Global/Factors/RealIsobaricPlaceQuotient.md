# The prescribed isobaric constituent at a real place

`HasRealIsobaricPlaceQuotient` records the real-place data needed for the
isobaric construction. It retains a parameter of each actual cuspidal
realization and the irreducibility of its standard module. The ordered
concatenation has an irreducible quotient that is also the image of a
surjective intertwiner on a stable subspace of the original standard module.

`hasRealIsobaricPlaceQuotient_of` uses the real branch of the generic
component bridge. An injective standard parameter into that component
is irreducible by stability of its image and nontriviality of the standard
module. The quotient on the sorted concatenation is obtained from the
largest proper stable subspace given by the real Levi quotient theorem.
The latter theorem uses the proved Levi chart integrability and integration
formulas. The three remaining inputs to the reduction are real generic
standard parameters, irreducibility of tied real standard modules, and
`RealStandardQuotientReorderingStatement`. The last input asks for
the same irreducible quotient to occur as a subquotient after reordering.

The local data implement the real-place constituent step in Getz and Hahn,
*An Introduction to Automorphic Representations* (2024), Theorem 10.6.4,
printed p. 286 (PDF p. 298), and Theorem 10.7.5, printed p. 288 (PDF p. 300).
The largest proper stable subspace gives the ordered quotient of Knapp,
*Local Langlands correspondence: the archimedean case* (1994), Theorem 1(a),
printed p. 400 (PDF p. 410). The reordering input is the subquotient
consequence of equal composition factors under permuting the blocks in
Badulescu and Renard (2010), Remark 2.3 and Proposition 2.4,
printed pp. 1123–1124 (PDF pp. 10–11).
