# Simultaneous standard conjugation from a dynamic realization

This is an internal adapter of published constructions. It does not translate
a new source assertion. Fix a connected reductive group scheme `G` over an
arbitrary field `k`, with `hG : IsConnectedReductive G`. This hypothesis
supplies the affine, smooth and connected structure used by cocharacter
conjugacy and the hypotheses of `relativeRootSignsDetermineDynamic`.
The input is one cocharacter `z` whose dynamic
parabolic and centralizer equal the all-test images of the specified maps
`p : P ⟶ G` and `l ≫ p : M ⟶ G`. The fixed target family is given by
a maximal split torus `i` and a generic cocharacter `ν`.

The adapter retains two explicit structural premises: conjugacy of maximal
split tori in smooth connected affine groups and `HasRelativeRootSystem i`.
It does not prove these premises or existence of the supplied simultaneous
dynamic realization.

First, `exists_innerIso_comp_eq_cocharacter` conjugates `z` into the fixed
torus. The published dominant-chamber move then supplies a normalizing
rational point whose action makes every positive relative-root pairing
nonnegative. The face of simple roots with zero pairing defines `J`; its
transported cocharacter `ζ` is standard for `J`.

The same product of the two rational points conjugates both subgroup
images. The proof transports their range equalities using the published
isomorphism-square range identity and functoriality of dynamic parabolics
and centralizers. Finally, the published relative-root sign theorem and
the supplied root system make all standard cocharacters for `J` give the
same dynamic subgroups. The standard intersections therefore equal the
dynamic parabolic and centralizer of this one `ζ`.

The conclusion gives all four all-test equalities at once: the conjugated
images equal `standardParabolic i ν J`, `standardLevi i ν J`, and the
dynamic parabolic and centralizer of `ζ`. The original `P`, `M`, `p`
and `l` are retained, with only ambient postcomposition by the one inner
automorphism. `simultaneousStandardConjugatingPoint` chooses such a point
with all witnesses. The result is over an arbitrary field and has no
extra characteristic, splitness or positive-rank premise.
