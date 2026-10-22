# Bounded descent through closed-ideal quotients

Author: Worker 36.

`Langlands.Analytic.BoundedQuotientStatement` concerns actual bounded algebra
homomorphisms between commutative normed algebras over a normed field. The
coefficient field, source algebra and target algebra have independent universes.
It asserts three properties:

1. A bounded map vanishing on an ideal also vanishes on its topological closure.
2. For a closed ideal, every bounded map vanishing on that ideal descends to
   exactly one bounded algebra map on the actual ring quotient, with agreement
   on every representative.
3. Whenever a bounded map on that quotient agrees with a given source map,
   every positive linear norm bound for the source map also bounds the
   quotient map, using the quotient norm.

No completeness, ultrametricity, nontriviality or normalization of the
algebra unit norms is assumed. The zero algebras and the whole ideal are
allowed. The third property is conditional on agreement and does not assume
the same bound as part of the descended map's data.

This is a derived normed-algebra prerequisite for the quotient presentations
in Berkovich's *Non-archimedean analytic spaces* (Trieste 2009), the opening
quotient-norm paragraph of section 2.1 and Definitions 2.1.1–2.1.2, p.7.
The source defines the quotient norm as an infimum over representatives and
uses it for admissible affinoid presentations. It does not separately state
this general normed-algebra proposition. Continuity makes the zero fiber
closed; algebraic descent and representatives approaching the quotient norm
give the claimed bounded descent. These arguments justify the extension
beyond complete nonarchimedean algebras.

The statement imports only the published bounded algebra map interface and
Mathlib's actual quotient and ideal-closure constructions. It assumes no
descended map as output in the existence clause and imports no proof of
this target. It supplies no claim that all ideals are closed, nor an
analytic-domain or structure-sheaf construction.

Registered original: `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
