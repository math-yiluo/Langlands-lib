# Pointwise etale descent in a flat scheme pullback

Let `f : X → S` be locally of finite presentation, and let `g : T → S`
be flat. Consider a cartesian square with projections `a : P → X` and
`p : P → T`. For a point `z` of `P`, suppose the actual local-ring map
of `p` at `z` is flat and formally unramified. Then the actual local-ring
map of `f` at `a(z)` is formally etale.

`SchemeEtaleFlatLocalDescentStatement` is the proposition asserting this
implication for arbitrary schemes in one arbitrary universe. All stalk
properties use the algebra structures induced by the displayed stalk
maps. The base change need not be surjective. The conclusion concerns
the chosen image point, and asserts no global etaleness of `f`.

This is an internal interface for the smooth equivalence relation slicing
proof. Its derivation uses faithful flatness of a flat local stalk map,
which applies to `a` because it is the base change of `g`. The two
compatible composite stalk maps show that the pullback stalk is flat over
the base stalk; faithful flatness reflects flatness to the original source
stalk. On affine neighbourhoods, the section-ring square is a pushout and
the stalks are localizations. Base change and localization for Kaehler
differentials, followed by faithful-flat reflection of their vanishing,
give formal unramifiedness of the original stalk map. Essential finite
presentation of that map and the flat local smoothness criterion then
give formal etaleness. This explanation records the provenance of the
statement; the declaration itself is a proposition awaiting proof.
