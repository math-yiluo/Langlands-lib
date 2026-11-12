# Central isogenies preserve split rank

This internal derived unit proves that a central isogeny between affine group
schemes over a field preserves the split rank defined by closed split subtori.
The groups need not be reductive or connected, and the field may have any
characteristic. It supplies the general transport step needed by the
quaternionic spin-group proof.

For the first inequality, take any closed split torus in the source and factor
its composite with the finite homomorphism through its closed split-torus
image. The factor map is finite because its composite with the closed image
inclusion is finite. `SplitTorusRankComparison` bounds the source torus rank by
the image torus rank. The closed inclusion bounds the latter by the ambient
target rank. Taking the supremum gives `splitRank_le_of_isFinite`.

For the opposite inequality, the published bounded-exponent theorem for the
full scheme-theoretic central kernel gives a split-torus power parametrization.
The published split-image construction turns it into a closed split torus in
the source mapping surjectively onto the chosen target split torus. The
published theorem `IsTorus.flat_of_surjective_hom` makes this map flat, hence an
epimorphism on underlying schemes. The reverse comparison from
`SplitTorusRankComparison` bounds the target torus rank by the lifted torus rank,
which is bounded by the ambient source rank.

The theorem `IsCentralIsogeny.splitRank_eq` combines the inequalities, and
`centralIsogenySplitRankStatement` gives the arbitrary-universe proposition
interface. All inputs are proved Library results from the imported modules;
the new content is their rank comparison and assembly, with no additional
external source assumption.
