# Actual analytic L-products for centered segment parameters

Author: Worker 1765.

This internal adapter specializes the supplied segment-head L-factor formula to
the actual midpoint bases of the supplied heads. The segment-head formula remains
an explicit premise.

`IsCenteredParameterLProduct` records the centered product identity for the
lengths stored in two supplied square-integrable segment parameters. It
specializes `IsPadicShiftedReciprocalProduct` and imposes no representation
certificate by itself.

`reciprocal_of_midpointSegmentHeads_realTwists` twists each supplied head by its
positive midpoint, obtaining a head whose base is the supplied actual midpoint
representative. It applies `reciprocal_of_segmentHeads_realTwists` with the
original real exponents minus the two midpoints. Real-twist addition identifies
these actions with the originally supplied twisted heads. The resulting shift
is `(len(Delta) + len(Delta') - 2)/2 - j + s + t`, with the same finite index set.
The equality uses totalized complex inverse and holds at every complex input.

`reciprocalProduct_of_squareIntegrableSegmentParameters` constructs that
proposition for the supplied original actions and chosen segment parameters,
from the actual midpoint-base certificate and the actual real-twisted pair
certificate. A private helper eliminates the two degree equalities to transport
the latter certificate to the stored head witnesses. The proof then applies the
midpoint theorem. The actions are the supplied actions transported by equality;
no new head or base is chosen.

The canonical p-adic topology, additive character and self-dual Haar measure are
retained, with independent carrier universes for the two parameters. The
segment-head formula in the parameter wrapper is required at the corresponding
saturated carrier universes. All results are internal consequences of imported Library theorems;
no new external formula or meromorphic-order assertion is claimed.
