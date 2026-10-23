# Finite rational descent for the actual quotient-algebra presheaf

Author: Worker 36.

The module defines proposition-valued proof targets. It proves neither
finite descent nor a sheaf property. All algebras, maps, intersections and
coverings appearing in the targets are the existing constructed objects.
In particular no output algebra, arbitrary restriction system, sheaf proof
or descent witness is a hypothesis.

`FiniteRationalGluingStatement` quantifies over a complete ultrametric
normed field K, a presented strict affinoid algebra P, a rational input d
over P, a finite index type I, rational inputs D(i) over P, and actual
locus inclusions f(i) : D(i) → d. All these carriers use one universe u.
The hypothesis `FamilyCovers d D` says every point in d's multiplicative
seminorm locus belongs to some D(i)'s locus. The family is finite but may
be empty. The inclusion arrows ensure each covering locus lies in the
target; these are separate from the point-covering condition.

For every tuple s(i) of elements of the actual quotient algebras D(i),
assume the two bounded restrictions of s(i) and s(j) to the constructed
intersection `(D i).inter (D j)` agree for every pair i,j. The conclusion
is that there is exactly one element a of the actual quotient `d.algebra`
whose restriction along each f(i) is s(i). The intersection uses the
published product denominator and products of the extended numerator
tuples. Its locus is the actual intersection, and its two restriction
maps are the ones constructed from the proved strict-test representation
property. This statement expresses degree-zero exactness of the finite
section descent diagram; it does not claim exactness of higher Cech terms
or admissibility as a sequence of Banach modules.

`RationalPresheafSheafStatement` quantifies over the same class of fields
and base algebras and asserts `CategoryTheory.Presheaf.IsSheaf` for
`rationalPresheaf K P` on `finiteRationalTopology K P`. This is the
existing commutative K-algebra-valued presheaf of actual rational quotient
algebras. The topology's covering sieves contain finite families of locus
inclusions that cover the target's points. Mathlib's categorical sheaf
condition asserts the corresponding compatible-family uniqueness and
existence after applying every covariant representable to the value
category; the usual limit formulation is equivalent. It is an assertion
about all covering sieves of this specific topology, not only a single
chosen covering family.

`RationalSheafStatement` is the conjunction of the two targets. Keeping
the concrete finite section assertion and categorical assertion named
separately permits a substantial algebraic descent proof followed by a
separate conversion to the site-theoretic sheaf condition. No equivalence
or implication between these targets is proved in this module.

Zero and nonreduced quotients, empty tuples and rational loci, and trivial
scalar valuations are allowed. An empty finite covering can cover only
an empty target locus; in that case the gluing assertion includes the
claim that the target quotient has exactly one element. The field is
complete, and rational radii are one. The represented-domain results
currently available in the project test presented strict affinoids only.
The targets neither broaden that test class nor assert a full analytic
G-topology comparison. They concern scalar-valued sections, not general
finite Banach modules. They do not construct locally ringed spaces,
atlases, etale or equivariant sites, or prove higher acyclicity.

The source is Berkovich, *Non-archimedean analytic spaces*, Trieste
lectures (2009), registered as `berkovich-2009-trieste-analytic-spaces`,
SHA256 `8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Definition 2.2.1 and Exercise 2.2.2(ii)–(iii), printed/PDF p. 9, supply
the rational quotient and intersection setting. Fact 2.2.6(i), p. 10,
is Tate acyclicity for finite affinoid coverings and finite Banach
modules. The concrete gluing target specializes its first two stages
to scalar sections on finite rational coverings, using the already
constructed quotient algebras and restriction maps. Exercise
3.2.5(ii)–(iii), p. 15, identifies affinoid functions with the affinoid
algebra and describes the structural sheaf for the full G-topology.
The categorical target is a derived restricted version on the present
finite rational site. These targets do not reproduce the source's
arbitrary positive radii, all-affinoid-domain framework or full quasinet
G-topology, nor the higher exactness and admissibility in Fact 2.2.6(i).
A proof must establish descent for the constructed quotients; citing
those source assertions or assuming their formal conclusions does not
supply a Lean proof.
