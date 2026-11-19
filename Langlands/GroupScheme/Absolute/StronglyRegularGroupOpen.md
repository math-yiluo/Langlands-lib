# A nonempty open of strongly regular points

`Langlands.GroupScheme.StronglyRegularGroupOpenStatement` gives a nonempty
open subset of a connected reductive group over an algebraically closed
field. At each rational point in that open, the centralizer on all tests
is represented by a maximal torus.

Choose a maximal torus and its nonempty open of strongly regular
points from `algClosedStronglyRegularTorusPoint`. The product projection
from the group times the torus is smooth, so the preimage of that open
is dense. Conjugation from the product is dominant by the result for
Cartan subgroups. The image of the preimage is therefore dense and is
constructible by Chevalley's theorem. It contains a nonempty open of
the group.

A rational point of this open has a nonempty inverse image in the
chosen open of the product. Taking a closed point of this inverse image
in the fibre yields a rational lift. The original point is the conjugate
of the torus coordinate of that lift. Commutation on each test is
preserved by the conjugation, and the conjugate torus stays maximal.
