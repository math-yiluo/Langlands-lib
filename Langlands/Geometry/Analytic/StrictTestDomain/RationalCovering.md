# Finite rational coverings over a fixed strict affinoid base

Author: Worker 36.

Fix a complete ultrametric normed field K and a presented strict affinoid
algebra P. The objects are the existing chosen `RationalData K P`, with
unit-radius inequalities on the actual multiplicative spectrum of P.
Morphisms are the existing inclusions of their loci; their bounded algebra
restrictions were constructed in `RationalCategory`.

`FamilyCovers d D` says that every point of `d.locus` belongs to some
`(D i).locus`. `IsFiniteCovering S` requires a finite index type I, rational
objects D i, and inclusion arrows D i → d lying in S, such that this family
covers d. The index type is in the scalar universe and may be empty.
No covering axiom or topology is supplied as an input.

The maximal sieve contains the singleton identity family. For stability
under pullback along c → d, the proof constructs each object
`c.inter (D i)` using the actual all-products rational intersection in
`RationalLimits`. Its arrow to c is `interLeft`; its arrow to D i is
`interRight`. The equality of parallel inclusion arrows and downward
closure of S put each first projection in the pulled-back sieve. The exact
intersection-locus theorem gives pointwise coverage.

For transitivity, choose a finite covering family of the pullback of R
along each arrow of a finite covering family in S. The composite arrows
belong to R. The dependent sum of the finite index types is finite, and
the two pointwise covering conditions give coverage by the composite
family. `finiteRationalTopology` uses these three proved facts to construct
an actual Mathlib `GrothendieckTopology` on this rational inclusion
category.

`mem_finiteRationalTopology` exposes its covering-sieve predicate.
`ofArrows_mem_finiteRationalTopology_iff` characterizes the sieve generated
by any finite family of inclusions: it covers precisely when the family
covers the target locus pointwise. In the forward direction, a point lies
in an object of a finite covering subfamily of the sieve; the defining
factorization of a generated-sieve arrow then places it in one of the
original family loci. The reverse direction uses the family itself.
`bot_mem_finiteRationalTopology_iff` proves that the empty sieve covers
exactly those objects whose locus is empty. The reverse implication uses
the empty index type, so empty loci are retained.

This is a derived finite rational topology over one fixed base and on
chosen presentations. It retains empty numerator tuples, empty loci,
zero or nonreduced quotient algebras, and trivial scalar valuations.
It does not identify different presentations of the same locus. It
constructs neither a structure sheaf nor Tate acyclicity, and asserts
no equivalence with the full analytic G-topology or an etale site.

The source context is Berkovich, *Non-archimedean analytic spaces*, Trieste
lectures (2009), printed/PDF pp. 9–10, Definition 2.2.1, Exercise
2.2.2(ii)–(iii), and the finite-affinoid-cover discussion before Fact 2.2.6;
p. 15, the definition of the analytic G-topology after Fact 3.2.4.
The registered source is `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
These passages motivate rational domains, intersections and coverings.
The finite-covering sieve construction here is internal categorical
packaging of the published actual rational loci and intersections.
The source's general domains and quasinet covers have a broader scope;
the Lean definition deliberately states the restricted construction.
