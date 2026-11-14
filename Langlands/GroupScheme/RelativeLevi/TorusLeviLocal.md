# Étale local Levi witnesses along a prescribed torus

Worker 592.

This derived construction combines the prescribed-torus presentation statement
with the dynamic local construction. All three proposition inputs remain
explicit: `RelativeTorusDynamicPresentationStatement`,
`DynamicRelativeLeviStatement`, and `RelativeUnipotentRadicalStatement`.
It does not discharge any of these inputs or assert a global Levi.

`RelativeLevi.TorusDynamicPresentation i t` consists of a cocharacter of
the given commutative group `T` whose composite through `t` and `i` has
dynamic parabolic represented by `i`. Representation is equality on every
test scheme together with monomorphy of the inclusion.
`TorusDynamicPresentation.baseChange` pulls such data along any morphism of
base schemes. The proof uses base change of represented subgroup functors
and `Dynamic.parabolic_baseChange`, then expands the base-changed composite
cocharacter. It imposes no flatness or reducedness restriction.

`TorusDynamicPresentation.witness` applies `torusDynamicLeviWitness` to this
data, a reductivity proof, and the two structure inputs. The resulting
`TorusLeviWitness` supplies an actual group scheme and relative Levi
inclusion containing the image of `t`, with uniqueness of its subgroup
functor among all relative Levi inclusions containing that image.

`RelativeLevi.EtaleTorusLeviData i t` packages an étale cover, dynamic
presentations on its members, and such Levi witnesses on those members.
`RelativeLevi.torusLeviEtaleData` constructs it under exactly the geometric
hypotheses of `RelativeTorusLeviStatement`, with the three statements listed
above as additional explicit inputs. It chooses the cover and cocharacters
from the presentation input. Reductivity of each actual pullback follows
from `IsReductive.baseChange`, and the dynamic construction supplies each
local witness.

The provenance is composition of the named Library interfaces; there is no
additional claim transcribed from the literature. Base change here transports
the presentation data. Relating chosen Levi witnesses on overlaps, effective
descent, and the global existence and uniqueness conclusion remain subsequent
obligations.
