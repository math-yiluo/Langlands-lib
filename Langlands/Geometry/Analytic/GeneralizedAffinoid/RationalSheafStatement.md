# Finite rational descent with arbitrary positive radii

Author: Worker 36.

This module defines three proposition-valued targets for the actual weighted
rational quotient algebras. It does not prove descent or a sheaf property.
The definitions adapt the published strict rational sheaf targets to the
existing positive-radius `RationalChart` category and `algebraPresheaf`.
No output algebra, restriction system, gluing witness or sheaf proof is an input.

`FiniteRationalGluingStatement.{u}` quantifies over a complete ultrametric
normed field K, a presented affinoid base P with arbitrary finite positive
polyradius, a rational chart d over P, a finite index type I, charts D(i)
over P, and actual arrows f(i) from D(i) to d. All these carriers use the
arbitrary universe u. Each chart has arbitrary positive relative radii and
coefficients whose actual classes generate the unit ideal. Its algebra is
the constructed complete weighted Tate quotient by the closed relation ideal.
An arrow retains an actual bounded K-algebra restriction over P; a mere
inclusion of loci is not assumed to produce such an arrow.

The separate hypothesis `FamilyCovers d D` says every multiplicative
seminorm point of d's locus lies in some D(i)'s locus. For any tuple s(i)
of actual elements of the D(i) quotient algebras, assume their restrictions
to every chosen pairwise intersection agree. The intersections and both
restriction maps are the published weighted product-denominator constructions.
The conclusion is that exactly one element of `d.algebra` restricts to s(i)
along every f(i). Thus this is scalar degree-zero finite descent, including
separation, for the actual quotient algebras.

`RationalPresheafSheafStatement.{u}` asserts Mathlib's categorical
`Presheaf.IsSheaf` for the constructed commutative K-algebra-valued
`algebraPresheaf K P` on `finiteRationalTopology K P`, for every such K and P.
A covering sieve contains a finite family of actual arrows whose loci cover
the target. The assertion concerns every covering sieve of that topology;
it is the categorical compatible-family condition, equivalently the usual
limit condition in commutative K-algebras. The arrows of the presheaf are
the actual bounded restrictions with only their norm and chosen presentation
forgotten. This target asserts neither a Banach-category sheaf nor a new
boundedness estimate for gluing.

`RationalSheafStatement.{u}` is the conjunction of the concrete finite gluing
and categorical sheaf targets. The separate names allow analytic descent
and the conversion for all covering sieves to be proved independently.
No implication between them is proved in this statement module.

Finite index types may be empty. The point-covering condition then forces
the target locus to be empty; the concrete target includes that the actual
target quotient has exactly one element in that case. Zero and nonreduced
quotients, empty numerator tuples, empty loci and trivial scalar valuations
are allowed. No nontriviality or strictness assumption is added.
The site uses the field-universe finite index convention of the existing
`FamilyCovers` and `IsFiniteCovering` definitions.

The source is Berkovich, *Non-archimedean analytic spaces*, Trieste lectures
(2009), registered as `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Definition 2.2.1 and Exercise 2.2.2(ii)-(iii), printed/PDF p.9, give the
positive-radius rational quotient and intersection setting. Fact 2.2.6(i),
p.10, supplies the stronger finite affinoid-cover Tate acyclicity statement;
the concrete target is its scalar degree-zero rational-cover consequence.
Exercise 3.2.5(ii)-(iii), p.15, identifies affinoid functions with their
algebra and describes the structural sheaf for the full G-topology.
The categorical target is the derived restriction of that sheaf assertion
to the existing fixed-base finite rational site. These original passages
were read directly. The targets retain arbitrary positive radii, while
remaining restricted to the stated rational site and scalar sections.

Higher Cech exactness, admissibility of Banach-module sequences, general
finite-module descent, the full analytic G-topology, locally ringed spaces,
analytic atlases and etale or equivariant sites are outside these targets.
A proof must establish the assertions for the constructed quotient algebras;
the source's assertions are not formal hypotheses.
