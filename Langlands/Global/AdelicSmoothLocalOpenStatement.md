# Smooth openness at every actual adelic-level local factor

This derived formulation isolates the local-openness input in Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
Theorem 4.5, printed p.12, first two proof paragraphs.

`AdelicSmoothLocalPointOpenStatement` is the conjunction of the curve-place
and number-field assertions. Fix an initial finite set `S`, two possibly
nonaffine schemes over its actual ring of S-integers, and a smooth relative
morphism between them. Both structure maps are locally of finite type and
separated. For every enlarged finite set `T` containing `S`, the induced
map on points over each actual local factor is open for the independently
defined affine-chart scheme-point topologies over the original S-integer
coefficient base. The coefficient actions are the original restricted
factor actions used by `AdelicModelOpenReductionStatement`.

For curve places the factors are the native completed fields at places in
`T` and their native completed valuation rings outside `T`. The local
assertion needs only fields `k` and `F` with an algebra structure; it
requires no global function-field finiteness or finite-constant premise.
This strengthening is justified by the complete rank-one discrete valued
nature of these actual completions. For number fields the factors include
every original infinite completion, the completed fields at supported
finite places, and the completed integer rings outside `T`. No factor is
removed. All objects live in an arbitrary common universe.

Conrad reduces local openness to smooth openness over complete nontrivially
valued fields and the open embeddings of integral points into field points.
The corresponding coefficient and base-change comparisons retain the
original topologies and point maps. Smoothness alone is the condition on
the morphism here: neither surjectivity nor geometric connectedness is
needed for local openness. Quasi-compactness of the structure maps is also
unnecessary for this local assertion, so local finite type is retained.

This file states the local assertion. Its proof is a separate obligation;
this statement does not assert almost-all integral surjectivity, uniform
Lang–Weil estimates, compatible spreading, or adelic openness. The source
Theorem 4.5 has these further hypotheses and conclusions, which remain
obligations of the whole-paper task.
