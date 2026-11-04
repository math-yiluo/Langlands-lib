# Second countability of finite-type local point spaces

This is a derived prerequisite for the countable-base assertion in Section 4
of Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed p.9. It uses the finite-coordinate topology of
Proposition 2.1, printed p.2, and the local-ring open-chart construction of
Proposition 3.1, printed p.4. The paper does not state this general local
second-countability lemma verbatim.

## Statement and hypotheses

Let R and S be commutative rings in an arbitrary common universe, with a
specified R-algebra structure on S. Give S a second-countable topological-ring
structure. No topology on R or continuity of its algebra map is required.

`AffineAlgebraPointSecondCountability` asserts that, for every finite-type
R-algebra A, the actual algebra-map point space `AlgPoint R A S` is second
countable in its existing evaluation topology.

`AffineSchemePointSecondCountability` asserts the same for actual relative
points `RingPoint R X S` of every affine scheme X locally of finite type over
Spec R, in the existing global-section evaluation topology. Affineness here
makes local finite type equivalent to finite type.

`SchemePointSecondCountability` further assumes that S is local and has
`IsOpenUnits`: its units form an open subset and inversion of units, viewed
in S, is continuous. It asserts second countability for the actual relative
S-points of every scheme X of finite type over Spec R, with exactly
`schemePointTopology R X S`. Finite type is expressed by
`LocallyOfFiniteType X.hom` and `QuasiCompact X.hom`.

`PointSecondCountabilityStatement` groups the two affine statements and the
last statement under its additional local-ring and unit hypotheses.
Hausdorffness, local compactness, separatedness and quasi-separatedness are
not assumed. The nonaffine statement retains quasi-compactness; it makes no
second-countability claim for an arbitrary locally finite type scheme.

## Provenance of the derived assertion

A finite-type algebra is a quotient of a polynomial algebra in finitely many
variables. The actual point map to the values of those variables is a
topological embedding into a finite power of S. A finite power of a
second-countable space, and every subspace of it, is second countable.
The existing affine scheme-point homeomorphism gives the affine scheme case.

Since Spec R is quasi-compact, a finite-type X admits a finite affine open
cover. Locality of S ensures that every actual point factors through a member
of the cover: select a chart containing the image of the closed point of
Spec S. Proposition 3.1's unit and inversion hypotheses make each chart map
an open embedding in the existing scheme-point topology. The map from the
finite disjoint union of chart-point spaces is consequently continuous,
open and surjective. An open quotient of a second-countable space is second
countable. This justifies the derived statement without a separation premise.

This pair declares a proposition target. Its Lean proof is a separate
contribution. Arithmetic stage products, full adelic second countability,
and generic-fibre comparisons require further applications.

## Source

Registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`:
printed pp.2 and 4, Propositions 2.1 and 3.1; printed p.9, Section 4.
