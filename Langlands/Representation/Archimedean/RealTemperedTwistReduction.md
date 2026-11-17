# Irreducibility transport under real determinant twists

This internal reduction concerns the Library's actual `O(n)`-finite real
standard modules. It uses `RealTemperedTwist.twistEquiv`, multiplication by
`|det|^s`, for a real number `s` and a rank-correct list of blocks.

Tensor induction extends the real-direction derivative identity of
`RealTemperedTwist` to every complexified Lie direction: the target operator
on a twisted vector is the twist of the source operator plus a scalar times
that vector. The scalar depends on the direction and the twist, not on the
vector. Every complex subspace is stable under scalar multiplication.
Consequently both the image and the inverse image under the twist of a
simultaneously compact and Lie invariant subspace are invariant.

The linear equivalence transports nontriviality and carries the zero and
whole subspaces to their counterparts. These facts prove
`RealTemperedTwist.isIrreducible_twist_iff`: the standard module of
`ds.map (realBlockTwist s)` is irreducible if and only if the standard module
of `ds` is irreducible.

`RealZeroExponentStandardIrreducibleStatement` is the still-unproved
irreducibility assertion restricted to lists all of whose real block
exponents are zero. The final two theorems prove its equivalence with the
unchanged `RealTemperedStandardIrreducibleStatement`. For a nonempty tied
list, choose a block with real exponent `e` and twist every block by `-e`.
Rank is preserved and all real block exponents become zero. Irreducibility
then transports back. For an empty list the zero-exponent hypothesis is
vacuous, so no choice of a block is needed.

These are internal derived transport statements, not a proof of the remaining
zero-exponent assertion. They use no Langlands quotient theorem or Langlands
classification input and leave the existing target and its imports unchanged.
