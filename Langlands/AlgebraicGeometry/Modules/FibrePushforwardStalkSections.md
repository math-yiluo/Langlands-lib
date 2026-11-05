# Pushforward stalks and actual fibre sections

Worker 1638 constructs the canonical additive map from the stalk of the
actual pushforward module at a base point to the global sections of the
actual residue-field fibre pullback. The map is defined by the colimit
universal property of the stalk. Its cocone uses the adjunction unit and
restriction that define `fibreNeighbourhoodSection`; the existing
restriction compatibility lemma supplies the cocone equations.

`fibrePushforwardStalkSection_germ` identifies its value on every represented
germ with that exact neighbourhood restriction. The range lemma represents
an arbitrary stalk element on a neighbourhood, chooses an affine
refinement containing the point, and restricts the representative. The
converse takes the germ of a given lift. The surjectivity equivalence follows
by quantifying over the fibre section.

These are internal sheaf-theoretic constructions for eventual fibre-section
lifting. They require no properness, noetherianity, flatness or ampleness.
They identify the stalk formulation in Stacks Project Lemma 30.21.3 with the
neighbourhood formulation of the published target, without proving the
cohomological surjectivity assertion. The retained original is
`stacks-noetherian-fibre-section-lifting-2026-11-03`, `02OF.txt`, Lemma 30.21.3
and its proof, in [Section 30.21](https://stacks.math.columbia.edu/tag/02OF).
The construction and the equivalence are derived from the Library's
`FibreNeighbourhoodSections` module and Mathlib's stalk colimit; the source
is used only to explain their role.
