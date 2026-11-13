# The split binary spin image in the parabolic elementary subgroup

This internal construction restricts the rational point maps of the existing
SL₂ spin lift and its scalar cocharacter to the actual parabolic elementary
subgroup of the supplied spin group.

The assumptions are an infinite field `K`, a finite-dimensional central division
`K`-algebra `D` of dimension four, a first-kind involution `σ` whose symmetric
subspace has dimension three, a quadratic form `q` on a finite index type with a
supplied hyperbolic pair, and a supplied spin cover `π : S ⟶ σ.isometryGroup q`.
The existing lifts retain the explicit premise
`CentralSimpleUnits.DegreeTwoNormOneSimplyConnectedStatement`.

`specialLinear_range_le_elementary` states that the full rational image of the
actual `specialLinear` lift is contained in `parabolicElementarySubgroup S`.
It applies the existing
`SpecialLinear.BinaryRoot.rationalPoints_range_le_parabolicElementarySubgroup`
to this lift. The target is connected reductive because it is simply connected
by the supplied spin-cover predicate. The imported theorem already proves that
every actual SL₂ homomorphism into a connected reductive group has elementary
rational image: the upper additive root contracts under the diagonal
cocharacter, its image lies in an actual geometric parabolic radical, and normal
generation by that root gives the full SL₂ image.

`specialLinearToElementary` is the original rational point homomorphism with
codomain restricted using this containment. Its underlying-map formula is
`specialLinearToElementary_coe`.

Since `scalar` is the upper diagonal cocharacter followed by `specialLinear`,
`scalar_range_le_elementary` follows by composition. The homomorphism
`scalarToElementary` restricts the original scalar rational point map, with
underlying-map formula `scalarToElementary_coe`.
The construction `scalarUnitsToElementary` has source `Kˣ`: it uses the inverse
actual affine Gm point equivalence over the identity test `Spec K`.
Its underlying-map formula is `scalarUnitsToElementary_coe`.
In particular `scalar_neg_one_mem_elementary` gives the elementary membership of
the scalar lift of minus one. All statements permit characteristic two.

The provenance is internal: this specializes the existing full split-binary
image theorem to the already constructed spin lift and uses the actual
rational Gm model. It proves the SL₂ and scalar contributions to elementary
generation. Elementary membership of the norm-one lift and the supplied spin
kernel remain separate obligations.
