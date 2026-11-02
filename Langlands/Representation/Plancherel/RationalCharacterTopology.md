# Actual rational norm characters in the canonical point topology

Author: Worker 200.

This adapter composes the existing actual character evaluation with the existing
local-field unit norm and source-positive integer order. Its source topology is
exactly `PointTopology.rationalPointTopology F G.X`, bound locally; it declares
no global topology instance on rational points.

The module imports the published `FieldUnitsTopologyProof` and uses its proved
`fieldNormUnits_isLocallyConstant` and `fieldOrderUnits_isLocallyConstant`.
No field-map continuity or local-constancy premise is added.

The field universe and characteristic are arbitrary, and G is any affine group
scheme over Spec F. Local constancy of both field-unit maps is pulled back along
`GroupScheme.continuous_rationalCharacterEval`. The resulting norm and integer
order are continuously bundled without changing their underlying evaluation
formulas. Closedness of the common norm kernel is the intersection of closed
equalizers. A continuous positive character is trivial on every compact subgroup,
so the actual common kernel contains each such subgroup without a local
compactness or nonarchimedean-group premise.

For the conditional portion, the canonical rational-point group is required
to have `NonarchimedeanGroup` and `WeaklyLocallyCompactSpace` instances. These
are explicit premises concerning that named topology; this module does not
construct them for arbitrary G. The published `commonNormKernelTopology`
then proves that the actual common kernel is open. The quotient topology is
discrete by this openness. The existing algebraic quotient-to-image equivalence
is therefore upgraded to a continuous multiplicative equivalence to the
existing explicitly discrete actual valuation image. Composing with the
canonical quotient map proves continuity of the actual image projection.
The existing unramified-character equivalence now receives that proved
continuity, retaining the stated point-group hypotheses.

Provenance: Waldspurger 2003, I.1, printed pp.239–240 / PDF pp.5–6,
`waldspurger-2003-plancherel`, and Renard, 9 July 2026 edition, V.2.3,
printed pp.105–106 / PDF pp.111–112,
`renard-2026-representations-groupes-reductifs-padiques`. These passages use
the actual norms and integer valuation coordinates to define G^1 and the
unramified characters. The present adapter is derived by composition and
application of published topology and kernel results. It assumes none of
the desired continuity, openness or discrete-image conclusions as structural
input. The actual norm retains the negative exponent of Waldspurger's
normalization through `LocalFieldUnits` and `RationalCharacterValuation`.

Finite rank, full-rank image lattices, finite-dimensional character tori,
comparison with the split-center real space, finite-index restriction,
algebraic-derived-subgroup point containment, split-center compactness,
measure normalizations and representation-theoretic conclusions remain
separate obligations. In particular, this conditional topology adapter does
not establish the topological-group premises for every reductive G(F).
