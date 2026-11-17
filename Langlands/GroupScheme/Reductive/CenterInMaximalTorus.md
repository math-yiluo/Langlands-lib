# The full scheme-theoretic centre inside a chosen maximal torus

This is an internal construction from the published centre existence,
maximal-torus centralizer, and commutative subgroup-intersection theorems.

The structure `CenterInMaximalTorus i` contains an actual commutative group
scheme, a homomorphism from it to the torus of `i`, and a proof that the composite
into the ambient group represents its full scheme-theoretic centre as a closed
subgroup on all test schemes. It makes no smoothness or reducedness assumption
on the centre.

For any connected reductive group over any field, and any supplied maximal
torus inclusion `i`, `centerInMaximalTorus` constructs this structure.
The proof chooses the existing full centre representative and intersects it
with the maximal torus. The intersection inherits its commutative group law
from the torus. Every central point belongs to the torus centralizer, which
equals that maximal torus by the published theorem. Therefore this intersection
still represents the entire centre. Its ambient inclusion is closed because
both inclusions in the composite are closed.

The choice of representative is noncanonical. Equality of its range with the
centre is an equality of all-test subgroup functors, retaining infinitesimal
and nonreduced test schemes in every characteristic.
