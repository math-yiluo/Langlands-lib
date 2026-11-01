# Exact-dimensional ample section cuts on irreducible schemes

`AmpleSectionExactDimensionStatement` consists of two internal geometric
assertions in an arbitrary common universe.

First, if a quasi-compact scheme `X` has topological Krull dimension equal to
a natural number `d`, then it has a point `x` closed in `X` for which the actual
local ring `X.presheaf.stalk x` has ring Krull dimension `d`. No Noetherian,
irreducibility or field hypothesis is imposed in this assertion.

Second, let `X` be an irreducible locally Noetherian scheme with topological
Krull dimension a positive natural number `d`. For every actual ample line
bundle `L`, there are `n ≥ 1` and a global section `s` of the actual tensor
power `L^n` such that its entire generation open `L.sectionOpen s` and its
complement are both nonempty, and

`topologicalKrullDim {x : X // x ∉ L.sectionOpen s} + 1 = d`.

The generation open is the published largest open on which the section map
from the structure sheaf is an isomorphism. The complement carries its
subspace topology. All dimension equalities and addition by one are in
`WithBot ℕ∞`, with the natural number cast into that type. The scheme is
quasi-compact in the second assertion because this is part of `L.IsAmple`.
The section's generation open is not asserted to be affine.

These are internal preparations for actual Euler positivity, rather than a
translation of an external theorem. For the first assertion, take a chain of
irreducible closed subsets of length `d`. A closed point in its smallest
member has coheight at least `d`, while the global dimension bounds that
coheight from above. The scheme stalk dimension equals that coheight.

For the second assertion, choose such a closed point `x`. Positive dimension
provides another point `y`. The published ample-section basis theorem,
applied to the complement of `{x}` at `y`, gives a positive-power section
which generates at `y` and vanishes at `x`. The proper-closed-subset inequality
in the irreducible ambient space gives the upper bound. A local frame at `x`
expresses the section by a nonunit scalar. The Noetherian local principal
quotient inequality and the embedding of its spectrum into the actual
vanishing set give the reverse bound.

Neither assertion requires smoothness, reducedness, equidimensional closed
stalks, a base field, or a rational point. The statement does not construct a
Cartier subscheme, assert regularity of the section, compute a coherent
cokernel's generic lengths, or prove Euler polynomiality or positivity.
