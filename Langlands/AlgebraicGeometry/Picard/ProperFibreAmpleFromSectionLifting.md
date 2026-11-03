# From eventual fibre-section lifting to fixed-bundle ampleness spreading

This internal module proves the implication from the published
`ProperFibrePowerSectionLiftingStatement` to the exact published
`ProperFibreAmpleSpreadingStatement`, in every universe. The lifting statement
is an explicit premise. This module does not supply its cohomological proof.

The proof first chooses a finite nonempty affine generation-open cover of the
ample fibre bundle in one positive degree. It raises all those sections to one
common degree above the lifting threshold, preserving every entire generation
open. The actual pullback–tensor-power isomorphism converts these sections to
sections of the pullback of the original bundle's tensor power. The finite
lifting interface provides lifts on one affine base neighbourhood.

Each lifted neighbourhood section defines a power section of the actual
restriction of the original line bundle. The open-subscheme/fibre bridge
identifies its generation open on the original fibre with the generation open
of the chosen fibre section; the two directions of the tensor-power
isomorphism cancel. The original fibre factors through this neighbourhood.
The affine map from the restricted family's fibre to the original fibre
transports both coverage and affineness to that restricted fibre.

The proper-fibre section-shrinking theorem now gives ampleness of that same
restricted bundle after another affine shrinking. The base-open conversion
returns an affine open neighbourhood in the original base and the actual
restriction of the original fixed line bundle, as required by the published
target. The definition `ampleNeighbourhoodOfPowerSectionLifting` chooses such
a neighbourhood together with all its stated properties.

The provenance is internal: the module composes the previously established
finite affine section cover, positive degree growth, simultaneous section
lifts, actual section restriction bridge, and proper geometric shrinking.
It does not add flatness, reducedness, a closed-point hypothesis, or a chosen
projective embedding. The remaining obligation is the explicit lifting
premise, not a change to the target proposition.
