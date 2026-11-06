# Characters of a dynamic parabolic and its centralizer

Let `G` be a group scheme over an arbitrary scheme `S : Scheme.{u}`, let
`ν : Gm S ⟶ G` be a cocharacter, and suppose `iP : P ⟶ G` and `iZ : Z ⟶ G`
represent its dynamic parabolic and centralizer. With `G` separated over `S`
and `iP` a closed subgroup, `parabolicCharacterEquiv` constructs an additive
equivalence from all rational characters of `P` to all rational characters
of `Z`. The forward map restricts along `centralizerToParabolic`; the inverse
restricts along the actual limit morphism `limitGroupHom`. The centralizer
need not be commutative. `character_eq_iff_restrict_eq` gives the resulting
criterion for equality of characters.

The proof starts with `comp_eq_comp_of_hasLimit_to_commutative`: a homomorphism
to a separated commutative group takes a point and any inner-cocharacter
limit to the same value. Indeed its image orbit is constant by commutativity,
and the image of the supplied limit is another limit of that orbit.
Separatedness gives uniqueness. This first lemma needs no separatedness of
the source.

`cocharacterToParabolicPoints` and its naturality proof lift the cocharacter
through the represented parabolic because its range lies in the dynamic
centralizer. `cocharacterToParabolic` represents this natural point map;
`cocharacterToParabolic_comp` verifies its composite with `iP` is `ν`.
The cocharacter lift itself needs no separatedness or closedness.

Assuming separatedness of `G`, the existing limit morphism takes each
parabolic point to its centralizer limit. Closedness of `iP` reflects this
ambient limit back into `P`, giving
`hasLimit_limitGroupHom_toParabolic`. Applying the first lemma on every
relative test and then the group-scheme point extensionality theorem proves
`hom_eq_limitGroupHom_comp`: every homomorphism from `P` to a separated
commutative group factors through the limit retraction. Applying this to
`Gm S`, whose separatedness follows from its construction as a base change
of an affine morphism, gives one inverse law of the character equivalence.
The other follows from the previously proved section identity for the
centralizer inclusion.

This is a derived construction from the existing dynamic limit,
closed-subgroup reflection and represented-subgroup interfaces. All point
statements concern every relative scheme test, including nonaffine and
nonreduced tests. It assumes supplied representatives and a closed parabolic
inclusion; it proves no existence of a torus, Borel subgroup, root datum,
highest-weight representation, big cell or Steinberg module. It does not
prove the universal `SteinbergBigCellStatement`.
