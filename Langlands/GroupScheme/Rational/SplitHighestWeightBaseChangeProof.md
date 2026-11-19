# Highest-weight base change and descent of semisimple representations

The theorem `Langlands.GroupScheme.splitHighestWeightBaseChange` proves the
unchanged published proposition
`Langlands.GroupScheme.SplitHighestWeightBaseChangeStatement.{u}`.
It applies in every universe, to every field and every supplied split pinning
of an affine group scheme, without additional hypotheses.

The scalar theorem restricts an intertwining endomorphism to the
one-dimensional highest-weight space, where it is multiplication by a scalar
in the base field. The difference from that scalar endomorphism has a stable
kernel containing a nonzero highest-weight vector. Irreducibility makes that
kernel the whole space.

The general affine operator-algebra theorem
`IsIrreducible.baseChange_of_scalar_intertwiners` then gives simplicity over
every extension field. Weight-space tensor extension preserves multiplicities,
and the transported root datum preserves the positive-root monoid. Together
with the newly proved simplicity, these comparisons transport the
highest-weight predicate. Its algebraic-extension specialization uses exactly
the pinning appearing in the published target.

To descend a simple representation over an arbitrary extension field, the
classification theorem gives its dominant highest weight. Character pullback
for the split torus is bijective and reflects dominance, so this weight comes
from a dominant weight over the base field. Classification realizes that
weight over the base field. Absolute simplicity and weight transport make its
extension a highest-weight representation of the same weight as the original
simple representation. The isomorphism clause of classification gives a
bijective actual intertwiner between them.

For semisimple descent, finite independent simple-subspace decomposition and
actual subspace coordinates provide a bijective intertwiner from a finite
direct sum of simple representations to the given representation. Descend
each simple factor as above. Their intertwiners form a block diagonal
intertwiner; block diagonal inverses show that it is bijective. The affine
matrix comparison identifies the sum of the extended factors with the
extension of the sum. Composing gives a bijective actual intertwiner from
the extension of the descended sum to the given representation.

The descended sum is semisimple because its canonical inclusions have simple
stable images spanning the whole space. Its coordinate dimension equals the
given dimension after extension, and finite coordinate dimension does not
depend on the field. A linear equivalence over the base field transports the
sum to coordinates indexed by the required `Fin m`. Semisimplicity transports
along this bijective actual intertwiner. Its inverse extends to the larger
field and composes with the previous intertwiner, giving exactly the
same-dimensional descent conclusion in the target.

All stability and intertwining conditions use every affine algebra test,
including nonreduced algebras. No rational-point density, algebraicity of the
arbitrary descent extension, or characteristic-zero hypothesis is used.
The implementation follows the direct scalar-line and finite-direct-sum route
described in the target's Markdown for Milne, *Algebraic Groups* (2017), 22.4
and 22.5; the classification and general absolute-simplicity inputs are proved
in their own modules.
