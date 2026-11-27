# Root signs and distance for the auxiliary parabolics

`isDistanceAdditive_to_opposite` uses the trivial intersection of opposite
unipotent radicals to verify the two inclusions that define the distance
condition for standard intertwining operators.

For a dominant auxiliary cocharacter, inclusion of the outer radical in the
auxiliary radical gives the positivity implication on roots through
`RelativeRoot.unipotent_le_iff_positive_rootSupport_of_smooth`. Applying the
same implication to the opposite root gives the negative sign implication.
When the outer pairing is zero, linearity reduces the auxiliary pairing to
the inner pairing. These facts give `auxiliaryCocharacter_pairing_pos_iff`
and `auxiliaryCocharacter_pairing_neg_iff`.

The two auxiliary cocharacters retain the sign of the inner cocharacter on
roots of the outer Levi and have opposite signs on all other roots.
`isDistanceAdditive_auxiliary` applies
`RelativeRoot.dynamicUnipotent_inf_le_of_positiveRoots` to the positive and
negative signs. It verifies the two radical inclusions of
`IsDistanceAdditive` for the triple consisting of the positive auxiliary,
inner, and negative auxiliary parabolics. The outer and inner cocharacters
are arbitrary and need not share a Levi. For a regular outer cocharacter
and zero inner cocharacter in split `GL₂`, the two auxiliaries give
opposite Borel subgroups, the middle parabolic is `GL₂` itself, and the
inclusions still hold.

The triple occurs in the definition of the two standard integrals in
Waldspurger V.1, printed pp. 288–289: `P_s = (M' ∩ s·P)U'`, `s·P` and
`P̃_s = (M' ∩ s·P)Ū'`. There `s·M ⊂ M'`, so the three parabolics have the
common Levi `s·M`. For three parabolics in `P(M)` with a single Levi `M`,
the two inclusions are the distance criterion
`d(P', P) = d(P', P'') + d(P'', P)` of IV.1(12), printed p. 283, under
which the standard intertwining operators compose. Without a common Levi,
IV.1(12) does not apply, and the lemma asserts only the inclusions. The
source is `waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

`auxiliaryCocharacter_neg_sameDynamicChamber` compares the negative of an
auxiliary cocharacter with the auxiliary cocharacter of the two negatives.
Their centralizers agree by `auxiliaryCocharacter_spec` and
`Dynamic.centralizer_groupHom_neg`. Their root signs agree by the two sign
criteria, so the two radicals agree by the smooth root-support criterion.
`Dynamic.parabolic_le_of_unipotent_le_of_centralizer_le` then gives equality
of the parabolics.

`auxiliary_realization_of_innerCocharacter` works with a closed
representative of the outer Levi and a cocharacter in that representative.
`auxiliaryCocharacter_orbit` gives equality of the two orbits on the outer
Levi. With the dominant inclusions from `auxiliaryCocharacter_spec`,
`Dynamic.realization_of_inclusions` gives the displayed extended
parabolic, Levi and unipotent radical.
`auxiliary_opposite_realization_of_innerCocharacter` also realizes the
opposite of the positive auxiliary through the negative outer parabolic,
using the opposite inner cocharacter and the same closed Levi inclusion.
