# Normalized geometric-character filtrations over the unramified field

This derived module fixes a nonarchimedean local field `F`, its actual maximal
unramified extension `K`, and its fixed separable closure. It tests actual
characters of a `K`-group after extension to that common separable closure,
using `algebraicExtensionAddValuation F` normalized by the original `F`-order.
It uses the norm Iwahori from any supplied finite Galois splitting field at
zero, and intersects it with those geometric character conditions at positive
depth.

The family decreases and is separated. The separation proof extends the
splitting from the supplied finite field to the separable closure, then uses
actual character separation there. The whole family is independent of the
finite splitting field, because its norm Iwahori is independent and its
positive character test uses one common closure. An actual torus morphism
preserves the family even with different source and target splitting fields:
pass to their compositum for the norm-image naturality and use actual
character functoriality for the common positive test.

The geometric-character conditions always imply the base character-valuation
kernel. This follows by identifying logarithmic zero with multiplicative
value one, then descending the original characters. For an induced torus,
`inducedTorusIwahori` identifies that kernel with the norm Iwahori. Thus at
positive depth its Iwahori intersection is redundant, and membership is
exactly the lower bound on the normalized additive value of every geometric
character minus one.

`localTorusSplittingData` obtains an actual finite Galois splitting field
inside the fixed closure from `exists_finiteGaloisSplittingField_inside`.
`localTorusFiltration` uses that choice to define a common family for every
actual torus, without a caller-supplied splitting field. Independence
identifies it with the construction from every other splitting field.
The module includes the decreasing and separated laws, containment in the
actual base character-valuation kernel, functoriality for actual morphisms,
and the induced-torus membership formula for these common families.

These are internal constructions from the published norm independence,
induced-torus Iwahori, actual characters and algebraic-extension valuation
APIs. They do not construct a centralizer filtration for groups with roots.

No openness or geometric root compatibility is asserted here.
