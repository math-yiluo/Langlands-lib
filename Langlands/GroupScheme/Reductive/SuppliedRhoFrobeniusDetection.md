# Whole-space Frobenius detection from supplied simple-root coordinates

This derived internal unit assumes a split pinning, integral coroot span,
and a `SimpleRootCoordinateFamily` over an algebraically closed field `k`.
Let `q : ℕ` be its exponential characteristic, expressed by `ExpChar k q`,
and let `r : ℕ` be the Frobenius height. The unit
proves injectivity of the actual same-height Frobenius restriction on the
entire canonical covariant space, its finite dimensionality, and the upper
dimension bound `(q^r)^N` for the number `N` of positive roots.
The supplied family is retained explicitly;
no existence of these structural inputs is asserted here.

A coordinate invariant under right height-r origin tests restricts to a
coordinate on the actual opposite dynamic unipotent representative. The
supplied-family simple-root degree cutoff makes that restriction invariant
under each full negative simple-root subgroup. The generic simple-root
stabilizer-envelope argument makes it constant on the whole unipotent group,
on every relative test scheme. The standard and dynamic representatives are
identified through their common all-test subgroup functor, so the identity
value statement applies to the actual restriction used in the target.

If restriction to the height-r quotient had a nonzero kernel, the generic
invariant-kernel theorem would give a nonzero origin-invariant member of
that kernel. Compatibility with the counit makes its identity value zero.
The preceding constancy forces its full opposite-unipotent restriction to
vanish, contradicting generic injectivity of restriction to the opposite
cell. This proves same-height detection for the entire induced space.

The supplied full reflection-word factors are lifted directly into the
standard representative of the same opposite unipotent functor. Their
ordered chart is bijective over every coefficient algebra by the full root
chart and monicity of the standard inclusion. Its pullback supplies pointed
polynomial coordinates on the actual coordinate algebra. The generic
Frobenius polynomial-box theorem makes the height-r quotient finite of
dimension `(q^r)` to the word length. A word listing every positive root once
has length `N`. Injectivity of restriction therefore makes the entire
covariant space finite and bounds its dimension by `(q^r)^N`, without a
calculation of Lie root dimensions.

The generic coordinate restriction, kernel and stabilizer-envelope steps
are reused. Canonical linked-root choices are replaced by the supplied
full family and its explicit rank-one degree cutoff. The proof does not
identify a regular dynamic subgroup as Borel and does not use the existing
unconditional canonical-rho Frobenius detection theorem. No new external
source claim is added.
