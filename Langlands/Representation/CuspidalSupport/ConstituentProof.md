# Cuspidal constituents of admissible product Levi representations

Authors: Worker 166 (final assembly and rank-zero argument) and Worker 196
(finite-type application).

`Langlands.CuspidalSupport.leviCuspidalConstituentTheorem` proves the exact
published proposition `LeviCuspidalConstituentTheorem.{uF, uV} F T B`.
It applies to every prime, actual p-adic field `F`, compatible topological
realization `T`, rank `n`, and block shape `B`, with independent field and
representation-carrier universes. Given an admissible smooth complex
representation `A` and an irreducible cuspidal actual subquotient `D`, it
constructs an injective intertwiner `D → A` and a surjective intertwiner
`A → D`. It imposes no finite dimension, semisimplicity, or fixed central
character on `A`. The two maps are not asserted to form a splitting.

## Implemented proof

For rank zero, `ConstituentRankZero` identifies the Levi with an empty
product and hence a subsingleton group. Linear sections and retractions
of the subquotient presentation are automatically equivariant and give
both required maps. This elementary extension uses no source theorem
about positive rank.

For the remaining ranks, put `H = determinantUnitOpenSubgroup T B`.
The published determinant-unit structure gives normality and finite index
of `H` joined with the center. The actual Levi is locally compact and
nonarchimedean by the published p-adic topology constructions.

The published block-isolation theorem supplies complementary invariant
subspaces `S,Q` of `A`. The restriction of `S` to `H` is semisimple, and
each of its irreducible subrepresentations is equivalent to a member of a
finite family `V` of irreducible subrepresentations of the restriction of
`D`. Moreover, `D` does not occur in `Q`. Complement transfer therefore
places the actual subquotient `D` in `S`. Admissibility of `S` follows
through its injective inclusion in `A`; admissibility of `D` is part of
cuspidality.

Each `V i` is nonzero by irreducibility. Reversing the equivalences supplied
by block isolation gives the type coverage expected by
`constituent_of_finite_types`. That ancillary lemma chooses a compact open
subgroup inside `H` which fixes a nonzero vector of `D` and meets every
irreducible type of `S`. Semisimplicity makes these fixed vectors generate
the restriction of `S`. Its admissibility supplies finite dimension of the
fixed space, so the published fixed-vector induction gives both maps
between `D` and `S`.

Finally, `constituent_of_isCompl` composes the embedding with `S → A`.
For the quotient map it uses the projection `A → A/Q`, the identification
`A/Q ≅ S`, and the surjection `S → D`. These are actual morphisms in the
published smooth representation category.

## Source and provenance

The target is Bernstein–Zelevinsky, *Induced representations of reductive
p-adic groups I* (1977), §2.4(b), printed p.447/PDF p.8, registered source
`bernstein-zelevinsky-1977-induced-i`. Its cited proof source is Bernstein
and Zelevinsky, *Representations of the group GL(n,F) where F is a
non-Archimedean local field* (1976), registered source
`bernstein-zelevinsky-1976-representations-gln`, English translation,
SHA256 `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
The original proof is Proposition 3.30, printed/PDF p.37, using the
decomposition of Proposition 3.28 and finite restriction of Lemma 3.26,
printed/PDF p.36. These passages were read directly.

The implementation follows the source's decomposition and fixed-vector
dimension induction, using independently published helper theorems. The
finite-type application explicitly ensures generation by the chosen fixed
vectors, needed to detect a nonscalar central operator in that fixed space.
It is an internal bridge between the published block isolation and
induction results; it assumes no additional theorem as input to the final
target. The rank-zero argument is an elementary internal extension.
The named statement and all its imported Lean/Markdown pairs are unchanged.
