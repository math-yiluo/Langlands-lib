# Actual intertwiner extensions for the tempered uniqueness argument

This internal construction exposes the algebraic splitting step used in the
uniqueness argument of Renard 2026, VII.2.6, printed page 231 / PDF page 237.
It composes Mathlib's semisimple-module extension property with the published
`admissibleUnitarySemisimplicity` theorem. It is not a proof of the full
uniqueness statement.

`IntertwiningRetraction i` consists of an actual complex-linear equivariant
map in the reverse direction together with its left-inverse law.
`semisimpleIntertwiningRetraction` selects this data for an injective map
into an algebraically semisimple representation. It uses the equivalence
between intertwiners and group-algebra linear maps, extends the identity map
from the injected module to the whole module, and transports the result
back. The original group and all three representation carriers have
independent universes; the construction imposes no topology on those
carriers and changes none of their actions.

`semisimpleIntertwiningExtension` composes an outgoing intertwiner from the
injected representation with that chosen retraction. Its output includes
the exact equality that restriction to the injected representation recovers
the original map. `nonzeroSemisimpleIntertwiningExtension` retains the same
map and proves it is nonzero when the original map is nonzero: a zero
extension would have zero restriction.

`admissibleUnitaryIntertwiningExtension` supplies semisimplicity from
admissibility and a specified invariant positive Hermitian form on the
target of the injection. It retains exactly the compact-open cofinality
hypothesis of the existing semisimplicity theorem and returns a nonzero
actual extension with the same restriction equality. No irreducibility,
finite length or smoothness hypothesis is added; the reused admissibility
predicate already includes smoothness of the ambient target.

For VII.2.6, the intended injected object is the original irreducible
representation, and the two ambient objects are its discrete-series
inductions. Their carrier universes may be larger than that of the
injected object. These definitions supply the nonzero map between those
ambient objects once the first induction is admissible and equipped with
an invariant positive form. Deriving those inputs for the actual parabolic
induction, passing to unitary Jacquet parts, and identifying conjugate
Levi data remain separate obligations. The construction does not assert
or prove an unconditional classification result.
