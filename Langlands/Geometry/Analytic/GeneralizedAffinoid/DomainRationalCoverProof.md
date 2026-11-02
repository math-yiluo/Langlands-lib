# Finite ambient rational coverage of full affinoid domains

`Domain.finiteRationalCover` proves the published
`Domain.FiniteRationalCoverStatement.{u}` at its full universe. For every
complete ultrametric normed field, every actual finite positive-polyradius
ambient presentation, and every full represented affinoid domain in it, the
conclusion gives a finite family of rational charts over that ambient algebra.
It retains actual arrows from the chart domains into the represented domain,
with the bounded algebra restrictions and structural commutativity in those
arrows, and covers every point of the domain locus.

The proof applies `finiteRationalCoverStatement_of_strictLocal` to
`StrictTestDomain.localRationalNeighborhood`. The assembly first makes a
finite sequence of independent completed Gauss Laurent field extensions. It
includes radius two to obtain a nontrivial valuation and simultaneously
realizes every presentation radius of the ambient algebra and the domain
algebra in the radical value group. Both transported algebras retain actual
positive-polyradius presentations; the transported domain retains its full
universal property and the composed continuous Gauss section.

Radical-radius strictification constructs strict presentations over this same
field and bounded algebra equivalences in both directions for the two
transported algebras. Conjugating the structural map and spectrum locus gives
the strict-test representation. The strict local theorem supplies, at every
point of that locus, an ambient unit-radius rational locus contained in the
domain and forming a relative neighborhood. Inverse transport of its
coefficients, with weighted-series representatives, gives a genuine rational
chart of the transported ambient presentation. Mapping its unit ideal proves
generation, and the full domain property constructs the bounded restriction.

Compactness of the transported domain locus selects finitely many such
rational neighborhoods. The finite-cover descent operation of the Laurent
reduction descends this actual cover through all Laurent steps, yielding
charts over the original ambient algebra and bounded restrictions to the
original full domain. The proof then unpacks this finite cover into the exact
published proposition.

No hypotheses are added to the original inputs. Arbitrary positive real
presentation and rational radii, trivial original valuations, nonreduced and
zero quotients, empty coordinate tuples and empty domains are retained. An
empty finite family is allowed. The supporting assembly's strict local
hypothesis is discharged by the imported proof theorem.
