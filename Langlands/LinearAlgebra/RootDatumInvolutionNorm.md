# Fixed coweights of an involution of an integral root datum

`Langlands.LinearAlgebra.exists_base_involution_norm` is an internal lattice
lemma for the real-points connectedness argument. The root datum is finite
and reduced, and its coroots span the integral coweight lattice. Given an
automorphism whose coweight action is involutive, the lemma chooses a simple
base on which each invariant coweight is a norm plus an integral combination
of simple coroots with fixed indices. The norm of `y` means
`y + σ.coweightEquiv y`.

The proof chooses an integral functional detecting every nonzero difference
between a coroot and its image, using the perfect pairing and
`SplitExistence.exists_dual_forall_ne_zero`. Subtracting the composite with
the involution gives an anti-invariant functional whose zero coroots have
fixed indices. The lemma `exists_base_coroot_nonneg` chooses a base on whose
simple coroots this functional is nonnegative. Those simple coroots form a
basis by `simpleCorootBasis`.

In the coordinates for the simple coroots with nonzero functional value, the
negative of the involution preserves coordinatewise nonnegativity. Indeed, it
maps those coroots to coroots of positive functional value, which are
nonnegative combinations of simple coroots. It maps each remaining basis vector
to its own negative, with zero contribution to the coordinates in question.

For an invariant `x`, take the lattice element `y` whose coordinates are the
positive parts of the coordinates of `x`. Both `y` and `y - x` have nonnegative
coordinates. Applying the preceding preservation property to them shows that
the residual `x - (y + σ.coweightEquiv y)` has nonnegative coordinates at the
nonzero simple coroots. The residual is invariant, so the same property makes
its negative nonnegative at those coordinates as well. They therefore vanish,
and the basis expansion puts the residual in the span of the fixed simple
coroots.
