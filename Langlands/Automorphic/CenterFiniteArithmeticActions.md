# Arithmetic actions on simultaneous center-finite adelic functions

Author: Worker 2.

This internal construction specializes actual arithmetic pullback to the existing
simultaneous center-finite adelic function spaces over an actual number field in
an arbitrary universe. The matrix rank is any natural number, including zero.
The coefficient field is complex, values are unchanged, and continuity uses the
inherited compact-open subspace topologies.

`centerFiniteSmoothGaloisAut` and `centerFiniteFiniteSmoothGaloisAut` are monoid
homomorphisms from the rational field automorphism group to continuous
complex-linear automorphisms. They precompose with the inverse arithmetic field
map, giving actual additive left actions. The second space includes a common
open finite stabilizer. Forgetting center finiteness gives exactly the previously
constructed smooth and common-stabilizer actions. Evaluation is substitution by
the inverse arithmetic adelic matrix map. Identity and multiplication follow
from the existing identity and contravariant composition laws. The action
instances are explicitly installable definitions, with no global instance.

Both actions intertwine the existing finite adelic right actions, with the
finite matrix pulled back by the same inverse field map. On the space with a
common finite stabilizer they also intertwine every genuine restricted
enveloping differential operator through the corresponding enveloping algebra
equivalence. The common annihilator of the whole smooth slice family transforms
by ideal preimage under the actual center algebra equivalence.

For a CM field, the corresponding `ComplexConj` equivalences use direct
arithmetic argument conjugation. They are involutive and equal the rational
Galois action at the CM involution restricted to rational scalars. Their
underlying smooth maps, evaluation, finite-action and differential covariance,
and common-annihilator preimage formulas specialize the same arithmetic
constructions. Complex character values are never conjugated.

On both spaces the existence of finite level is preserved and reflected. The
specified central character follows the existing Hecke-character Galois or CM
action, with the latter evaluated as `chi(ideleClassComplexConj x)`. For CM
conjugation the actual standard infinite compact is invariant, so finiteness of
its translate span is preserved and reflected as well.

Provenance is internal composition of `CenterFiniteArithmeticTransport`,
`SmoothArithmeticActions` and `FiniteDifferential`. The inverse-pullback action
law, inherited subspace maps and covariance specialize their actual
constructions. No new original-literature identification, derivative topology,
growth, cuspidality or automorphic occurrence is asserted.
