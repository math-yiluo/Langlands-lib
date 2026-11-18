# Actual associativity of three coefficient extensions

`BasicAtlas.baseCompHom_assoc` proves the whole integral formal-map equation
between the two ways of collapsing three actual coefficient extensions. On each
test chart, the maps have the original transition series between independently
selected parent charts. The two transition cocycle equations identify each
composite with a single original transition. The actual
`baseSource_sourceChart` equality identifies the initial selected chart of the
two routes. The proof neither assumes injectivity of coefficient maps nor
equality of the intermediate source selections.

`OrderAction.baseCompIso_assoc` lifts this equality to the actual full-order
isomorphisms, including their stored inverses. Equality elimination transports
it through the supplied intermediate and final scalar algebra structures in
`baseCompReAlgebraIso_assoc`. Specializing those structures to three supplied
algebra maps gives `baseAlongCompIso_assoc`. The actual composite coefficient
maps agree by the definitions of composition.

`baseAlongAssociativityTestSquare` retains the two actual composite formal
maps on each test chart, the actual identity maps on the common target, and
the rationalization of the proved whole integral equality. Both forward and
inverse rational maps come from the specified integral isomorphisms.

This is internal coherence of the existing atlas coefficient constructions.
The coefficient ring, acting ring, and rational field have separate universes,
and the finite coordinate type is arbitrary. The integral associativity
requires no domain assumption; rationalization uses the existing domain and
fraction-field hypotheses. Covers may be infinite and coefficient maps may
merge principal generators. No criterion for detecting global rational tensors
from charts, framed composition law, or representability is asserted.
