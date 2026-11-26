# Coordinate rings on affine opens and their reductions

For a scheme over `Spec R`, the chart of an affine open has its actual
`R`-algebra structure. Pullback of functions along a map of such opens
commutes with the chart maps to the schemes. Across a quotient `R → R/L`,
the section square of the pulled-back affine open is a ring pushout, so its
ring of functions is the quotient by the extended ideal. The comparison
identifies the actual map of sections with the quotient map. On spectra it
identifies the induced map of the two charts.

These comparisons are derived from the affine pullback formula and the
standard computation of a pushout along a quotient of rings. They implement
the affine tests for the difference-of-lifts calculation in SGA 1, Exposé III,
Proposition 5.1.

The ring comparison is natural under maps carrying one open into another.
For residue coefficients this follows by checking on representatives in the
original chart ring, where both sides are composites of maps of sections.
The same compatibility holds on spectra for every ideal quotient. Nilpotent
quotient maps are surjective on the underlying scheme, and affine opens
pull back to affine opens.

The infinitesimal comparison uses `sga1-arxiv-math-0206203v2`, Exposé III,
Proposition 5.1, printed pp. 59–60 (PDF pp. 75–76), SHA-256
`8e64218d356456c534eebf996940f0f957e43b54f1a080241debe12cbaf60d3c`.
