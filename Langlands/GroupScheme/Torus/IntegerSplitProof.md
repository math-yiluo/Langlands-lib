# Every torus over the integers is split

Workers 193 and 665.

`Langlands.GroupScheme.integerTorusSplit` proves
`Langlands.GroupScheme.IntegerTorusSplitStatement.{u}` in every universe.
Given an étale-locally split torus over the spectrum of `ULift.{u} ℤ`, it
gives a finite coordinate type and a group-scheme isomorphism with the
corresponding split torus over that spectrum.

`RelativeTorus.IsTorus.isMultiplicativeType` first makes the given torus a
group of multiplicative type. The proof applies
`integer_isDiagonalizable_of_normalIsotrivial` to the published theorem
`multiplicativeTypeNormalIsotrivial`. The reduction uses the irreducibility
and normal stalks of the lifted integer spectrum to get a finite étale
surjective cover on which the group is diagonalizable. The arithmetic
section theorem supplies a section by the finite étale consequence of
Minkowski's theorem. Pullback along the section recovers diagonalizability
over the integer spectrum itself.

`RelativeTorus.IsTorus.isSplitTorus_of_isDiagonalizable` identifies the
fixed character group of that diagonalizable model with the finite free
character group of a split torus. It reads these coordinates from a residue
field in one of the original split charts, which exists since the integer
spectrum is nonempty. It uses the resulting character group isomorphism
to construct the splitting of the original group scheme over the base.

This implements the integer-torus example following Corollary B.3.6,
p. 293, in Brian Conrad's *Reductive group schemes* (2014), registered as
`conrad-2014-reductive-group-schemes`. The finite étale cover in the proof
comes from the corollary and the arithmetic argument uses a section of
that cover. [Conrad, Corollary B.3.6](https://math.stanford.edu/~conrad/papers/luminysga3.pdf#page=293)
