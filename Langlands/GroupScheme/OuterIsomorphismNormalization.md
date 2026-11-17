# Outer quotients represented by fixed points of normalization

This internal construction represents normalized isomorphisms by an equalizer
in relative schemes. Its input is a natural normalization of all test points of
a supplied `GroupIsomorphismScheme`, invariant under the supplied automorphic
action, together with a unique acting point taking each normalized point to
the original point. These inputs remain hypotheses. This module does not
construct pinned normalization for reductive groups or prove the DVR existence
statement.

`PointNormalization` quantifies over every relative scheme test and every
refinement. The action is the existing inverse-precomposition action
`GroupIsomorphismScheme.actionHom`. Its decomposition field asserts existence
and uniqueness of a point of the acting group on the original test, with no
requirement to lift it to the original group.

Naturality identifies normalization with postcomposition by the normalization
of the universal point. Invariance and the decomposition imply that this
endomorphism is idempotent: normalize an orbit expression for the original
point and cancel the action by invariance.

The normalized parameter scheme is the equalizer of this endomorphism and the
identity. Idempotence factors normalization through the equalizer, and the
resulting class map retracts the inclusion. Thus the equalizer represents the
fixed points on every scheme test, including nonreduced and disconnected tests.

For the orbit map from the acting group times the equalizer, existence follows
from the input decomposition and factorization of normalization. To prove
uniqueness, normalize an equality of two orbit expressions. Invariance and
fixedness identify their equalizer coordinates; the equalizer inclusion is a
monomorphism, so those coordinates agree. Uniqueness in the input decomposition
then identifies their group coordinates. The previously defined
`outerOfNormalizedSection` turns this all-test bijection into an actual product
isomorphism by Yoneda and constructs `PointNormalization.outer`.

Only flatness and quasi-compactness of the acting group over the base are
additional geometric hypotheses for this outer quotient. No finiteness,
separation, or étaleness conclusion about the normalized scheme is asserted.

The provenance is internal and derived: the construction uses the universal
property of equalizers, naturality, and group action laws. All normalization
properties needed by this categorical representability step are explicit inputs.
