# Full finite rational coverage from strict local Gerritzen–Grauert

This internal assembly takes the proposition
`StrictTestDomain.LocalRationalNeighborhoodStatement.{u}` as an explicit
hypothesis. It constructs an actual `Domain.FiniteRationalCover U` for every
full represented domain `U` over every actual positive-polyradius ambient
presentation over a complete ultrametric field `K : Type u`.

`nonempty_finiteRationalCover_of_strictLocal` first uses
`LaurentReduction.exists_strictifiable` to obtain a common complete pure Laurent
field in the original universe. Its valuation is nontrivial, and every
presentation radius of both the transported ambient algebra and the
transported domain algebra is in its radical value group. The reduction
retains the actual full domain and the operation descending finite ambient
rational covers along the composed Gauss sections.

Apply `RadicalStrictification.exists_strictPresentation` separately to those
two actual presentations. This gives strict presentations over that same field
and actual bounded algebra equivalences in both directions. For each point of
the transported domain locus,
`nonempty_rationalNeighborhood_of_strict` conjugates the full domain
representation through these equivalences, applies the supplied strict local
theorem, and transports its strict rational neighborhood to an actual rational
chart over the transported ambient algebra. The chart retains a bounded
restriction into the transported full domain.

`FiniteRationalCover.ofNeighborhoods` uses compactness of that domain locus to
choose a finite family of these relative neighborhoods. `D.descendCover` then
descends the resulting actual finite ambient rational cover through all the
Laurent steps to a finite rational cover over the original ambient algebra,
with its actual bounded restrictions. This uses the established finite-union
neighborhood descent at Gauss section points; no claim that a single upstairs
chart always descends to a single chart is needed.

`finiteRationalCoverOfStrictLocal` chooses a cover from this proved nonempty
type. `finiteRationalCoverStatement_of_strictLocal` forgets only the packaging
and concludes the published `FiniteRationalCoverStatement.{u}`, still with the
strict local theorem as a hypothesis.

The provenance is internal composition of the actual Laurent field-domain
construction, radical-radius strictification, bounded strict comparison,
compactness and rational-cover descent. No strictness, nontriviality,
reducedness or nonzero condition is imposed on the original inputs. Arbitrary
positive real radii, trivial original valuations, zero and nonreduced
quotients, empty coordinate tuples and empty domains are retained. This unit
does not prove strict local Gerritzen–Grauert and is not an unconditional proof
of the host finite-cover proposition.
