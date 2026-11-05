# Standard cocharacters in the actual rational norm kernel

This is an internal consequence of the published integral relative Weyl actions,
root reflections, character restriction and intrinsic cocharacter evaluation.
It supplies a geometric prerequisite for the norm-kernel compact-restriction
argument. It does not prove uniform coefficient support.

Let a torus map injectively into an ambient group scheme over a field, with
finite actual rational relative Weyl group `W`. For an integral cocharacter
`ζ`, define `normKernelCocharacter i ζ` to be
`|W| • ζ - ∑ w : W, w ζ`. No division or rational cocharacter is used.

Every ambient rational character restricts to a Weyl-fixed torus character,
because inner conjugation acts trivially on it. The proof reuses
`relativeWeylLatticeAction_torusCharacterRestrict` and the published equality
of the full-character action names from `RelativeWeylFaithfulness`. Moving each Weyl action across
the lattice pairing therefore shows that this restriction pairs to zero with
the corrected cocharacter.

When the torus is split and each actual relative root admits a relative
reflection, the published Weyl-average lemma says that every root pairs to
zero with the sum. Consequently its pairing with the corrected cocharacter
is `|W|` times its original pairing. The Weyl group is nonempty, so this
preserves vanishing on a standard subset and strict positivity on its
complement. Thus every standard cocharacter gives a corrected standard
cocharacter for the same subset. The existence of the finite Weyl group and
root reflections remains explicit here.

The actual rational character of a cocharacter value at **any** field unit is
the unit raised to its integral pairing. This follows by restriction to the
torus and the published intrinsic evaluation theorem. For the corrected
cocharacter all ambient rational characters therefore evaluate to one. Over
a nonarchimedean local field, its image in the ambient rational points lies
in `Plancherel.rationalCommonNormKernel`.

This unit constructs neither an escaping sequence nor an Iwahori basis. Those
are subsequent geometric obligations, as is the class-uniform support bound.
