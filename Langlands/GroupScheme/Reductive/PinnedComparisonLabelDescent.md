# Descent of pinned comparison labels to every original test

This module gives a conditional reduction of the constant outer-isomorphism
chart to precise local classification inputs. It does not discharge those
inputs. It is internal infrastructure for the chart proof.

`OpenPinnedLabelCompleteness M N hAffine` is a proposition: every
concretely `IsLocallyPinned` direct comparison between `M,N` over any common
scheme agrees on a neighbourhood of each point with a canonical
`ComparisonLabel` representative. The representative uses the exact affine
pinned theorem `hAffine`. The label records the entire character-lattice
map. The proposition asserts equality of the actual comparison on that
open neighbourhood, beyond merely equality on points or root weights.

## Original-test labels

`existsUnique_label_of_locallyPinned` assumes this local completeness
input. For a relative test `T` and all-test family `F` whose recovered
direct comparison is concretely pinned, it produces a unique morphism
from `T` to the actual constant scheme of lattice labels classifying `F`.
Choose the neighbourhood and label at each point. Their inclusions form
a Zariski open cover, including an empty covering family when `T` is
empty. The direct/iterated comparison equivalence converts each actual
comparison equality into equality of natural local families. The local
labels are actual morphisms to the constant scheme via its component
inclusions. All-test injectivity of `constantPinnedFamily` makes these
morphisms compatible, and subcanonical descent glues the unique global
morphism. This global morphism allows the label to vary locally on `T`.

`existsUnique_label_of_fppfLocallyPinned` extends the same classification
to the concrete `IsFppfLocallyPinned` predicate. Pull back to its supplied
single fppf cover, apply the preceding Zariski classification there, and
descend the resulting constant-scheme morphism along that fppf cover.
Once again injectivity supplies compatibility, and subcanonicity descends
the label to the original test. `classifyPinnedFamily` chooses the unique
label, and `refine_classifyPinnedFamily` states its classification equation.
No global lifting or globally constant label on the test is assumed.

## Orbit and chart reductions

`constantPinnedFamily_orbit_bijective` retains three inputs: the exact
affine pinned theorem `hAffine`, the pair's `OpenPinnedLabelCompleteness`,
and `HasFppfLocalPinnedRepresentatives` for normalization. The latter input
constructs the existing natural normalization with predicate
`IsFppfLocallyPinned`. The labelled representatives are normalization-fixed
by the preceding constant-family module. Every normalized local family
has a unique original-test label by fppf classification above. The generic
representation-free normalization theorem then proves the all-test
bijection

`(d,b) ↦ (constantPinnedFamily.refine b).twist innerAction d⁻¹`.

Here `d` is an adjoint point on the original test and `b` is a morphism
from that test to the actual constant scheme. This result requires no
isomorphism representer.

`pinnedOuterIsomorphismChart_of_localCompleteness` retains the same exact
affine and normalization inputs and local completeness for every pair.
It proves the unchanged `PinnedOuterIsomorphismChartStatement` from them:
classify the representation-free family in the arbitrary supplied `I`,
and transfer the orbit bijection using the universal family. The quotient
and Isom representative in that statement remain arbitrary. All tests,
including nonaffine, disconnected, nonreduced, and empty schemes, are
included. These conditional theorems do not assert the unconditional
chart statement until all three inputs have been supplied.

## Provenance

The implemented proof uses categorical Zariski and fppf descent of
morphisms, the existing full-lattice representative family, and the
published natural normalization and full-centre adjoint discrepancy
interfaces. It isolates the local completeness input of the pinned
classification argument. This is a derived internal reduction, rather
than a separate claim quoted directly from the literature.

The canonical test-to-base map uses the published name
`LocalGroupIso.terminalBasePoint`.
