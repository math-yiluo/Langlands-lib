# The right-limit subgroups of the minimal congruent torus filtration

`minimalCongruentRightLimitFromCongruence` gives an actual subgroup
whose set of points equals the union of the strictly deeper subgroups.
For a torus over the maximal unramified field of a nonarchimedean local
field, its model input is the smooth first congruence model of the
connected Néron model. The two point identities for that input specify
its first congruence points and its higher congruence points. The latter
are those of the connected Néron model with the level increased by one.

At two depths with equal integer part, monotonicity follows from the
decreasing shallow groups. At a positive integer congruence level, the
class of smooth models containing the shallow subgroup grows as the
fractional depth increases, so the congruence intersection decreases.
Across an integer boundary, a deeper point lies in the congruence
subgroup of the connected Néron model with level at least the next
integer. The addition identity places such a point in the appropriate
congruence subgroup of the first congruence model. This model extends
to every smooth model containing the shallow group, because the first
congruence points are generators of every shallow term. At depth below
one, containment in the first congruence group suffices directly.
The subgroups at depths greater than a given depth form a directed
family for inclusion, so their union is the underlying set of their
subgroup supremum.

This is derived from Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), registered as `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
See Lemma A.5.13(3), printed p. 636 / PDF p. 667, Definition B.5.2,
printed p. 667 / PDF p. 698, and Definition B.10.8 and Proposition
B.10.10, printed p. 690 / PDF p. 721. The depth subgroups use
Definition B.10.8 as amended in `kaletha-prasad-2024-corrections`,
version of 1 November 2024, PDF p. 50, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
