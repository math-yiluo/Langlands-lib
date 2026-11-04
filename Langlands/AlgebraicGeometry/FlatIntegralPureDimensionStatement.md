# Pure dimension under injective flat integral extensions

This internal prerequisite supports the field-extension part of the fibre
property in Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed pp. 5–6, Theorem 3.4(2). The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Conrad does not state the separate ring-theoretic result here. It is an
internal algebraic tool, whose precise hypotheses and conclusion are below.

`Langlands.AlgebraicGeometry.SchemeFiberGeometry.FlatIntegralPureRingDimensionInvariance`
is a proposition in two independent universes u and v. It quantifies arbitrary
commutative rings R and S, an R-algebra structure on S, flatness of S as an
R-module, integrality of the algebra map, injectivity of that map expressed by
`FaithfulSMul R S`, and a natural dimension d. It asserts equivalence of
`HasPureRingDimension R d` and `HasPureRingDimension S d`. Each predicate
requires dimension d for the quotient by every actual minimal prime.

No Noetherian, finite-type, field or nontriviality condition is assumed. The
zero-ring case is included. The statement concerns every component, not only
the total Krull dimension. Flatness is needed to ensure that contraction of a
minimal prime is minimal; integrality compares the corresponding quotient
ring dimensions; injectivity ensures a minimal prime upstairs exists over
every minimal prime downstairs. These descriptions explain the intended
proof route and do not supply proof assumptions in the proposition.

For an algebraic extension of fields, base-changing an arbitrary algebra
provides such a flat integral injective extension. The proposition alone
neither constructs that application nor proves invariance under arbitrary
transcendental field extensions, constructibility of fibre loci or filtered
descent. Those remain separate obligations.
