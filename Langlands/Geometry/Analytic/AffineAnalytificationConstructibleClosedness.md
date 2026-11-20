# Closed constructible subsets under the affine analytification center

Let `K : Type u` be complete, ultrametric and nontrivially normed. For a
commutative `K`-algebra `A : Type v` with finite polynomial presentation `P`,
the center of a point of `Space K P` is the kernel of its multiplicative
seminorm. Suppose that `s` is constructible in `Spec A` and that a maximal
ideal `m` specializes from a point `p` of `s`. The construction
`constructibleClosurePoint` chooses a point over `m` in the analytic closure
of the full center preimage of `s`. In particular, a closed full preimage
detects closedness of `s`.

Choose a basic constructible piece of `s` containing `p`. In the domain
`A ⧸ p`, its nonvanishing condition is a principal open defined by a nonzero
element. The published density lemma supplies a limit of extending
seminorms nonvanishing on that element. The limit vanishes on the image of
`m`, and maximality identifies its kernel. The seminorm embedding and range
comparison give a point in the closure in the affine polynomial-locus space.
The continuous map induced by the quotient sends the approximating subset
into the center preimage of the chosen piece and sends the limit to a point
with center `m`.

Closedness of the preimage therefore forces `s` to contain every maximal
specialization of its points. If an arbitrary specialization were omitted,
one basic constructible piece of the complement would contain that point.
The Jacobson property gives a maximal specialization in the same piece,
contradicting the maximal case. Mathlib's constructible specialization
criterion then gives closedness of `s`.

The form proved here is an internal consequence of the center and seminorm
comparisons and `SeparatedAnalytificationDensity`. It gives the affine
closedness implication of Berkovich, *Spectral theory and analytic geometry
over non-Archimedean fields* (1990), Corollary 3.4.5 after Proposition 3.4.4,
printed p. 65 (PDF p. 79), in the registered source
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`.
