# Discrete-series orbit transport under Levi conjugation

Waldspurger uses the orbit `sO` and the inducing class `sω` at every
parabolic in `P(s.M)` in VI.3, printed p. 306 (PDF p. 72), and tests
`sO = O'` in Remark VII.2.4, printed p. 320 (PDF p. 86).
See *La formule de Plancherel pour les groupes p-adiques (d'après
Harish-Chandra)*, source `waldspurger-2003-plancherel`. The unitary
unramified characters in these orbits use the rational-character norms
of I.1, printed p. 239 (PDF p. 5).

`conjugateLeviModel` postcomposes the actual inclusion with the inner
automorphism carrying the source Levi to the target Levi. The formula
for its point homeomorphism proves that every algebraic norm character
transports by composition with the inverse point conjugation.
`unitaryCharacterConjugation` uses this identity and the canonical
model comparison to identify the full unitary unramified character
groups. Its value on a target point `m'` is the original character
evaluated at `g⁻¹m'g`. `splitCenter_map_leviPointConjugation` follows
from the actual point image formula and the published
`splitCenterChoiceIndependence`.

`conjugateDiscreteSeriesClass` applies the existing discrete-series
pullback along the inverse point conjugation. It sends the target
quotient Haar back to the source quotient along
`quotientLeviConjugationSymm` and uses `haarMemLpInvariant` to compare
square-integrability with respect to the given source Haar. The
quotients carry their stated Borel measurable structures. Local
compactness and second countability come from the actual closed Levi
and the topological group quotient. The Haar comparison here concerns
the square-integrable class predicate.

Pullback commutes with the unitary twisting action, so `conjugateOrbit`
is defined on the actual orbit quotient. For the chosen models of the
intrinsic family, `conjugateFullIndex` uses this orbit at the given
target parabolic. The formula `orbitConjugates_conjugateFullIndex`
identifies its entire constituent set with the image under actual
pullback. Surjectivity of `unitaryCharacterConjugation` supplies the
reverse inclusion. Under the explicit centralizer containment of the
source Levi, `existsUnique_weylTransports_of_levi_eq` realizes this
construction at any relative Weyl element and any parabolic with the
required conjugate Levi. Uniqueness follows from the previously proved
fixed-Weyl uniqueness for the constituent relation. This gives the
index transport used by the actual average and by association counting.
The source-normalized integral identities and the V.3 coefficient
comparison are separate obligations.
