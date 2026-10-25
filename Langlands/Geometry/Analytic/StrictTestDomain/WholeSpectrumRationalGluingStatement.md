# Scalar rational descent over the whole spectrum

Author: Worker 101. The focused target and its division from relative gluing
were specified by Worker 135.

`Langlands.Analytic.StrictTestDomain.WholeSpectrumRationalGluingStatement`
is a proposition-valued definition, not a theorem or an assumption of descent.
It quantifies over a complete ultrametric normed field K, a presented strict
affinoid algebra P over K, a finite index type I, and rational input data
D(i) over P. The scalar field, base algebra and index type use the same
arbitrary universe u. No nonempty or chosen enumeration of I is required.

The covering hypothesis says that every point of `BanachSpectrum P` belongs
to the unit-radius rational locus of some D(i). Given a section s(i) in each
actual quotient `(D i).algebra`, suppose that its restrictions along
`interLeft (D i) (D j)` and `interRight (D i) (D j)` agree for every i,j.
The conclusion is that there exists exactly one element a of P such that
`(D i).baseMap a = s i` for every i.

The quotient algebras are the existing closed-ideal Tate quotients constructed
from the denominators and numerator tuples in `RationalData`. The overlap is
the existing `RationalData.inter`, using the product denominator and pairwise
products of the denominator-extended numerator tuples. Its locus is the
intersection of the two loci. Both restrictions are the published bounded
algebra maps from the factor quotients to this intersection quotient. They
are constructed using the proved strict-test representation property and
agree with `RationalIntersection.leftMap` and `rightMap`. No output algebras,
restriction system, sheaf condition, exactness assumption or descent witness
is supplied as an additional hypothesis.

This is scalar degree-zero descent over the whole base spectrum: exactness
at P supplies uniqueness, and exactness at the product of the quotient
algebras supplies existence for compatible families. It does not assert
higher Cech exactness, admissibility of Banach-module maps, or descent for
general finite Banach modules. It has no arbitrary target rational datum d.
The relative `FiniteRationalGluingStatement` and the categorical sheaf
statements remain separate targets; none of them is changed or proved here.
Relative comparison and transport to a cover of d's algebra, and conversion
to a categorical sheaf, require separate work.

Empty index types, numerator tuples and rational loci, zero and nonreduced
algebras, and trivially valued scalar fields remain in scope. If I is empty,
the covering hypothesis forces the base spectrum to be empty, and the
conclusion asserts that P has exactly one element. This includes a genuine
empty-cover obligation for a future proof. No reducedness or nontriviality
assumption is inserted to avoid it. All radii are one. The imported
representation results test presented strict affinoids; this target neither
extends them to all affinoid tests nor identifies the full analytic
G-topology.

The original source is Vladimir G. Berkovich, *Non-archimedean analytic
spaces*, Trieste lectures (2009), registered as
`berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Definition 2.2.1 and Exercise 2.2.2(ii)-(iii), printed/PDF p. 9, give the
rational quotient setting and intersections. In Exercise 2.2.2(ii), the
single denominator g in the input tuple and the relations gT_i - f_i
fix the interpretation of the displayed rational inequalities despite the
source's inconsistent g_i and m/n subscripts. We specialize all radii to one.
Fact 2.2.6(i), p. 10, asserts exactness and admissibility of the augmented
Cech complex for finite affinoid coverings and finite Banach modules.
Taking M = A and retaining injectivity and exactness at the first product
gives the mathematical provenance of this derived scalar target. The exact
Lean formulation in the present quotient API is internal packaging, not a
separately named source theorem. Exercise 3.2.5(ii)-(iii), p. 15, supplies
broader structural-sheaf context; it is not a sheaf hypothesis here. The
source permits arbitrary positive radii and general affinoid domains, while
this statement uses only the existing unit-radius strict constructions.
The retained original was checked directly, including the displayed formulas
on pp. 9-10; no source-specific errata note was present in the registered
project errata locations. Source assertions provide provenance, not a Lean
proof of analytic descent.
