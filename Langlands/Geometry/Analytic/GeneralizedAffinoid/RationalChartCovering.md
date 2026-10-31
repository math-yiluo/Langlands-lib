# Finite point coverings of actual positive-radius rational charts

Authors: Worker 56 and Worker 36. The finite-covering sieve proofs adapt
Worker 36's published `StrictTestDomain.RationalCovering` construction to
the category whose arrows are actual bounded quotient maps.

Fix a complete ultrametric normed field K and a presented affinoid
algebra A. Objects are the existing `RationalChart K A`: chosen rational
data with arbitrary positive radii and a proof that the coefficient
classes generate the unit ideal. Their algebras are the constructed
closed rational quotients. Arrows are actual bounded algebra maps in the
opposite direction, with their equation over A proved. A locus inclusion
alone is not used to construct an arrow.

`FamilyCovers d D` says that every point of `d.locus` belongs to some
`(D i).locus`. Given actual arrows `f i : D i → d`,
`familyCovers_iff_jointlySurjective` identifies this condition with joint
surjectivity of the constructed maps on multiplicative seminorm spectra.
The forward implication lifts a base point to the chosen source quotient
using its spectrum/locus homeomorphism, then proves equality with the
given target point by injectivity of the target homeomorphism and the
over-base equation of `f i`. The reverse implication lifts a base point
to the target quotient, applies joint surjectivity, and uses the same
over-base equation to prove membership in a source locus. This equivalence
does not require finiteness or completeness of K.

`IsFiniteCovering S` requires a finite index type I, charts D i, and
actual arrows `f i : D i → d` belonging to S, whose loci cover d.
The index type lies in the scalar universe and may be empty.
The maximal sieve contains the singleton identity family. For pullback
stability along `c → d`, use the explicit all-products intersections
`c.inter (D i)`. Their constructed bounded maps give the actual arrows
`interLeft` to c and `interRight` to D i. Proven uniqueness of actual
restrictions identifies the two parallel composites to d; downward
closure of S puts each left projection in the pulled-back sieve.
The exact intersection-locus equality proves coverage of c.
This argument requires neither a categorical pullback of charts nor a
construction of restrictions from arbitrary locus inclusions.

Transitivity chooses a finite covering family of each pullback of R
along the arrows in a finite covering family of S. Composing the actual
arrows gives a family in R, indexed by the finite dependent sum of their
index types. Successive pointwise coverage proves that this family covers.
`finiteRationalTopology` constructs a Mathlib `GrothendieckTopology` using
these proofs; no covering axioms are inputs.

`mem_finiteRationalTopology` exposes the covering predicate.
`ofArrows_mem_finiteRationalTopology_iff` proves that the sieve generated
by a finite family of actual arrows covers exactly when its loci cover.
The forward implication uses the defining factorization of an arrow of
the generated sieve and the proved inclusion associated to the factoring
restriction. The reverse implication uses the family itself.
`bot_mem_finiteRationalTopology_iff` characterizes coverage by the empty
sieve as emptiness of the locus, using the empty index type in the reverse
direction. `bot_mem_finiteRationalTopology_iff_isEmpty` translates this
to emptiness of the actual quotient spectrum through its homeomorphism.

This is an internal finite rational topology over one fixed presented
affinoid, on chosen data and actual bounded maps. It retains empty
numerator tuples, empty loci, zero and nonreduced quotient algebras,
trivially valued scalar fields and arbitrary positive radii. The original
unit-generation condition is retained; no equivalence with the source's
no-common-zero condition is asserted. The construction does not prove
that every locus inclusion is represented by an arrow, identify all
presentations of the same locus, or construct a structure sheaf,
acyclicity theorem, atlas or etale site. No equivalence with the full
analytic G-topology is asserted.

Source context: Berkovich, *Non-archimedean analytic spaces*, Trieste
lectures (2009), printed/PDF p.9, Definition 2.2.1 and Exercise
2.2.2(ii)–(iii), for rational domains and their intersections; p.10,
Fact 2.2.3(i) and the finite-affinoid-cover discussion preceding Fact
2.2.6; p.15, the paragraph defining the G-topology after Fact 3.2.4.
Registered source: `berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
These passages motivate the rational loci, intersections and covering
families. The source's G-topology uses general analytic domains and
quasinets. The finite-covering sieve construction and its spectrum
criteria here are derived from the published concrete chart constructions
and are not claimed as separately numbered results in the source.
