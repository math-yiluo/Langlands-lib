# A commutative subgroup inside its represented whole-group centralizer

Author: Worker 1348.

This is an internal derived construction from the published all-test centralizer,
represented-subgroup factorization and maximal-torus predicates. It assumes no
rational Levi existence, reductive-center theorem or parabolic structure result.
It applies over an arbitrary base scheme until the explicitly field-specific
maximal-torus statements.

For `b : B → G` from a commutative group scheme and an actual homomorphism
`j : M → G` representing `torusCentralizer b`, `torusCentralizerFactor b hj`
is the canonical map `B → M`. The published self-centralizing containment
`range b ≤ torusCentralizer b` supplies the factorization. Its composite with
`j` is `b`, and it is central in `M` on every test scheme and refinement.
Centrality follows by mapping each commutation equation along the monomorphism
`j` and applying the defining centralizer condition in the opposite order.
The general lemma `isCentral_of_range_le_torusCentralizer` implements that
argument without requiring a representing equality.

If both `b` and `j` are closed subgroup embeddings, the factor is closed as
well. Over a field, a split subtorus therefore gives a central split torus
inside this representative. Ambient maximal splitness passes inward by the
published closed-subgroup transfer. The corresponding inward transfer for
maximal tori reuses `IsMaximalTorus.of_comp` from `Torus.MaximalTransport`
and applies it to the canonical factor.

These constructions require a supplied centralizer representative. They prove
neither its existence nor that it is a rational Levi. In the minimal-parabolic
proof route, they provide the central split torus inside a Levi once the
geometric centralizer identification has been proved. They impose no
centrality assumption in the ambient group and make no reduction to rational
points.
