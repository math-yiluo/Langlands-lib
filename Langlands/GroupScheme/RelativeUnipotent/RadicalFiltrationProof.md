# Finite vector-bundle filtrations of supplied relative unipotent radicals

`Langlands.GroupScheme.relativeUnipotentRadicalFiltration` proves
`Langlands.GroupScheme.RelativeUnipotentRadicalFiltrationStatement.{u}` at an
arbitrary universe. For every affine base and every supplied relative
unipotent radical of a parabolic in a reductive group, the radical has the
finite series required by `RelativeUnipotent.HasFiniteVectorBundleSeries`.

The proof extracts a finite étale cover by affine charts from the
quasi-compactness of the base. On each chart the term indexed by `d` uses the
root groups of face weight at least `d + 1`. The term comparisons on overlaps
identify the subgroup ranges on every test. Descent gives smooth closed
global terms, closed normal successive inclusions and their represented full
fppf quotients. The term indexed by zero identifies with the supplied radical.
All chart weights are bounded by `D.bound`. At that index the local terms are
trivial, and the global term is trivial on every scheme test by reflection
from the cover.

For each successive quotient, the two original chart identifications on a
common affine parameter differ by the canonical comparison of the restricted
full fppf quotients. The coefficient isomorphism and the coherence of point
lifting through pullbacks identify its coordinates with those of the
original quotient charts. On each parameter test the comparison acts by
matrix multiplication in the global functions of the test. In either chart
the prescribed scalar operation on the original point is coordinatewise
scalar multiplication. Matrix multiplication commutes with this operation,
and the coordinates of the second chart recover the point. Thus the two
original scalar operations agree on common affine tests.

Affine refinement reflects the scalar agreement to arbitrary tests. The
original section transitions therefore give actual linear module
isomorphisms on overlaps. Their compatibility on points proves their cocycle
identity. Effective descent of the finite locally free module gives the
vector-bundle additive structure for the actual global quotient. The
finite-series construction applies to these quotients and the terminal
triviality, and transports the series to the supplied radical along the
initial isomorphism. The construction accommodates disconnected and
non-noetherian affine bases, with the original finite ranks prescribed
locally by the charts.

The source is Brian Conrad, *Reductive group schemes* (2014), Theorem 5.4.3,
p. 174 and proof pp. 175–177, including Lemma 5.4.4 on p. 176. The Lean proof
uses the common finite weight bound on its cover and constructs linear
descent by comparing the original full quotient maps and their point charts.
