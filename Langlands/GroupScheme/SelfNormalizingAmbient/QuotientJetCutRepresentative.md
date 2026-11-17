# Actual cut representatives of retained quotient jet ideals

Let `G` be affine over `Spec R`, let `i : H → G` be an actual closed
subgroup, and let `D : ProperQuotientJetData i Q` be the retained data
for a supplied homogeneous quotient. Write `B` for the chosen ambient
coordinate algebra and `I = D.ideal`.

`D.cutGroup` is the existing actual corepresented subgroup with
coordinate algebra `B/I`, constructed from the cut-out condition
supplied by `D.ideal_range`. `D.cutInclusion` is its actual homomorphism
into the fixed corepresented ambient group. Its underlying scheme map
is exactly the spectrum of the quotient map `B → B/I`.

`cutInclusion_range` proves equality with the original subgroup in
ambient coordinates on every relative test scheme. The imported
all-test comparison between actual subgroup membership and membership
in its affine-point family identifies both sides with the same
classifying algebra map vanishing on `I`.

`cutRepresentativeIso` is the actual group-scheme isomorphism from `H`
to this quotient-coordinate subgroup. Both inclusions are monic and
represent the same all-test subgroup functor, so the existing uniqueness
theorem for representing subgroups constructs the isomorphism.
`cutRepresentativeIso_hom_comp` proves inclusion compatibility;
`cutRepresentativeIso_hom_left` states it explicitly with the spectrum
of the quotient map.

This is an internal consequence of the imported actual cut subgroup,
all-test ideal, and representer uniqueness APIs. It adds no smoothness
or reductivity assumption beyond the supplied data. The jet quotient
comparison, conjugacy comparison, and Grassmannian kernel equality
remain separate obligations.
