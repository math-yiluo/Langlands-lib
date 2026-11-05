# Affine neighbourhoods of a section

For a scheme morphism `f : X → Y` with an actual section `e : Y → X`, and
each point `y` of `Y`, `affineSectionNeighbourhood f e he y` constructs
affine schemes `T` and `W` with open immersions into `Y` and `X`, a
morphism `W → T`, and an actual section `T → W`. The image of `T` contains
`y`. Both morphisms commute with the original morphism and its section.

This is an internal construction from Mathlib's affine open basis and
scheme pullbacks. Choose an affine open `U` around `y`, an affine open `V`
around `e(y)` inside the inverse image of `U`, and an affine neighbourhood
`T` of `y` in `U` on which the section lands in `V`. Set
`W = V ×_U T`. Both factors and the base are affine, so `W` is affine.
The map `W → V` is an open immersion by base change of `T → U`.
The section is the pullback lift of the restriction of `e` and the identity
of `T`; its compatibility follows from the original section equation.

Any morphism property local at the source and stable under base change
passes from `f` to `W → T`: compose with the open immersion `T → Y`,
use the commuting square and restriction along `W → X`, then cancel
the open immersion. In particular smoothness and local finite
presentation restrict. Since `W` and `T` are affine, `W → T` is
quasi-compact and quasi-separated. Thus locally finite presentation of
`f` gives finite presentation of the constructed neighbourhood.

The construction imposes no finiteness or separation hypothesis on `X`
or `Y`. It supplies the affine shrinking step needed in the relative
identity-component argument. It asserts no openness of a union of
fibre components and does not prove the group-specific reduction or
relative identity-component existence.
