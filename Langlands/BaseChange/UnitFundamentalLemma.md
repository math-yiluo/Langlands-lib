# The unit fundamental lemma

This proves `Langlands.BaseChange.UnitFundamentalLemmaStatement` with the two
field universes independent. The target is Henniart–Lemaire (2011), §I.3.1,
Proposition, printed p. 25, attributed there to Kottwitz (1980), Lemma 8.8.
The proof uses the finite unramified extension in the statement.

The spherical unit is the indicator of the spherical subgroup. For the ordinary
and twisted orbital integrals of these indicators, the compact-open formula
expresses the result as the sum of masses of the contributing double cosets,
converted from extended nonnegative masses to a complex integral. Any
contributing ordinary coset supplies a spherical conjugate of the scalar
extension of the norm. The integral cyclic norm lift therefore makes the
ordinary orbital integral vanish at every regular non-norm.

For an associated pair, if the extended ordinary element has a spherical
conjugate, evaluate a single unit from the monogenic integral order to get a
cyclic norm lift integral on every such conjugate. The norm-fibre conjugacy
theorem gives an element `s` taking the twisted element to this lift by
σ-conjugation. The ordinary coset of `y` corresponds to the twisted coset of
`s * baseChange y`. This is a bijection on the contributing cosets by the
spherical double-coset comparison.

Regularity makes the scalar-extended centralizer commutative, so the
conjugators of the norm have the same action on the twisted centralizer. The
associated measure equality can therefore use `s`. Apply this equality of
pushforward measures to the open set of elements whose conjugate by
`baseChange y` is spherical. Its preimages are the twisted stabilizer at
`s * baseChange y` and the ordinary stabilizer at `y`, using spherical subgroup
reflection for the latter. Their masses are equal. Both spherical subgroups
have mass one, so the compact-open quotient mass formula gives equal summands
on the two sides. Reindexing the sums proves concordance.

If the extended ordinary element has no spherical conjugate, both sets of
contributing cosets are empty. On the twisted side this follows by taking the
cyclic norm of a spherical twisted conjugate and conjugating it by the given
association witness. The compact-open formula then gives zero on both sides.
