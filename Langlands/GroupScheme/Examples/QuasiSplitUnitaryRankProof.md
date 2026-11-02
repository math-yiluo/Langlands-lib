# The ranks of the quasi-split unitary group U(1,1)

Workers 1225 and 37. The theorem `Langlands.GroupScheme.QuasiSplitUnitary.rankStatement`
has exactly the published type `Langlands.GroupScheme.QuasiSplitUnitary.RankStatement.{u}`.
For fields `F E : Type u`, the given quadratic extension, a finite basis of the
matrix algebra, and a nonidentity `F`-automorphism `c` of `E`, it proves the
three conclusions for the existing unitary group scheme. It adds no hypotheses
and covers characteristic two. This is an internal proof from the published
matrix, torus, and splitting interfaces; its route is described below.

The first conclusion is `isClosedSubgroup_cocharacter` from
`QuasiSplitUnitaryCocharacterClosed`. Its affine pullback on coordinate rings
contains the two Laurent generators: natural diagonal matrix coefficients
pull back to nonzero scalar multiples of `t` and `t⁻¹`. Constants, addition,
and multiplication by those generators give surjectivity. The affine
closed-immersion criterion then proves that the hyperbolic cocharacter is a
closed subgroup.

For the second conclusion the proof chooses a finite enumeration of `I` from
the given `Finite I` instance and applies `splitTorus_rank_le_one` from
`QuasiSplitUnitaryRankBound`. The actual universal torus matrix has orthogonal
idempotent coefficient matrices, whose nonzero support has size at most two.
The unitary inverse identity makes this support stable under negation, so all
weights lie in `{a,-a}`. If `I` has at least two elements, a nonzero integer
vector orthogonal to `a` gives a one-parameter Laurent-valued torus point
whose matrix image is the identity. Injectivity of affine matrix coordinates
and cancellation of the given closed immersion imply that the torus point
is itself the identity, forcing every coordinate exponent to vanish. This
contradicts the chosen nonzero vector. The companion rank-bound Markdown
details the coefficient and specialization arguments.

The third conclusion is `exists_rankTwo_splitTorus` from
`QuasiSplitUnitarySplitTorus`. The block Levi in `GL₂` for the distinct integer
weights `1,-1` consists of diagonal invertible matrices and is naturally
isomorphic to the split torus indexed by `ULift (Fin 2)`. Compose its closed
inclusion with the inverse of the existing unitary splitting isomorphism over
`E`. This gives a closed split torus with two factors in the actual base-change
group scheme. The distinction of these weights is in the integer lattice,
so it persists in characteristic two.

The Lean assembly is the conjunction of these three lemmas. The published
target and its imported files are unchanged. A successful compilation of this
proof is distinct from independent review, exact-target validation, and publication.
