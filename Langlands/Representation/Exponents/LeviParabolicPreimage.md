# Actual inverse images under a supplied Levi retraction

Worker 1452. This is internal scheme-theoretic preparation for
`LeviParabolicExtensionStatement`; it does not yet prove parabolicity or the
geometric radical assertions of that target.

Over any base scheme, start with actual maps `l : M → P`, `r : U → P`,
normality of the range of `r`, and an isomorphism of the supplied
Levi-first multiplication. The published `leviRetraction` gives `P → M`.
For any actual `q : Q → M`, the new group is the group-scheme pullback
`P ×_M Q`. Its projection to `Q` has a canonical section induced by `l`.
The original `U` maps into this pullback, and its range is exactly the
scheme-theoretic kernel of the projection on every relative test scheme.

If the original radical map is monic, multiplication of the section by that
same radical is an isomorphism. The implementation applies the published
kernel-complement theorem, using the split projection and the exact kernel
identity just proved. No field, topology, cocharacter, or representability
assumption beyond the displayed actual maps is introduced.

For monic `l`, the intersection in `P` of the original Levi range with
the inverse-image range is exactly the range of `q ≫ l`. After any monic
original ambient map `p : P → G`, the same intersection identity holds in
`G`, and the inverse-image range is contained in the original outer range.
These are identities of subgroup functors on arbitrary test schemes,
including nonreduced schemes. Their proofs use the pullback universal
property and the equality `l ≫ leviRetraction = 𝟙 M`, never density of
rational points.

The construction and proofs are derived internal content from the published
Levi retraction, subgroup preimage, and kernel-complement interfaces. The
intended geometric application is the inverse-image construction described
in the unchanged target's Markdown; the present file proves only the
explicit algebraic and functorial assertions stated above.
