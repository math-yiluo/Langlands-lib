# Actual points in a standard etale presentation

Author: Worker 208.

`standardEtalePointHomeomorph` identifies the actual K-algebra-map points
of a standard etale A-algebra B with the subtype

    {(p, x) : AlgPoint K A K × K | f.eval₂ p x = 0 and g.eval₂ p x ≠ 0}.

Here f, g and the generator of B come from Mathlib's actual
`StandardEtalePresentation A B`, and p denotes the underlying ring map when
used in `eval₂`. The point spaces have the published `AlgPoint` evaluation
topologies; the displayed space has the product and subtype topologies.
The forward map restricts an actual B-point to A and evaluates the generator.
The inverse uses the presentation's universal property, with the A-algebra
structure on K induced by p. Its underlying ring map respects K because
the scalar tower K -> A -> B commutes.

The construction assumes that K is a nontrivially normed field, and retains
independent universes for K, A and B. Completeness is unnecessary. Neither
A nor B is required to be finite type over K. No abstract point or topology
package is assumed.

Joint polynomial evaluation is continuous by polynomial induction: a monomial
is the product of a continuous coefficient evaluation and a power of the root
coordinate. For each b in B, Mathlib's
`StandardEtalePresentation.exists_mul_aeval_x_g_pow_eq_aeval_x` supplies a
polynomial h and an exponent n such that b*g(generator)^n = h(generator).
Consequently the inverse coordinate map evaluated at b is

    h.eval₂ p x / (g.eval₂ p x)^n.

The denominator is nonzero everywhere on the coordinate subtype. This proves
inverse continuity in the actual evaluation topology. The same fraction
identity proves that restriction and the generator determine every point,
and hence the two maps are inverse. Forward continuity follows from
continuous restriction and generator evaluation.

This is a derived construction supporting the local etale/smooth openness
reduction in Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(2011), printed p.11, the discussion preceding Theorem 4.5. The registered source
is `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The explicit presentation and homeomorphism are our implementation bridge,
not a separately numbered assertion in that source.
The construction does not assert that the coordinate projection is open or
that every smooth morphism has been reduced to this presentation. Those
analytic and geometric obligations remain separate.
