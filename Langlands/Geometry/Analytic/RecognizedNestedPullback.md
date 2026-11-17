# Actual pullback squares between nested recognized affinoid pieces

Author: Worker 310.

This internal construction concerns an actual strong map `g` between the
local-domain enlargements of affinoid atlas presentations `A` and `B`.
Let `P₀`, `P` be recognized source subsets and `W₀`, `W` recognized target
subsets. Suppose `g(P₀) ⊆ W₀`, `W ⊆ W₀`, `P ⊆ P₀`, and
`P = P₀ ∩ g⁻¹(W)` as literal ambient subsets.

`recognizedNestedPullbackEquiv` constructs a bounded algebra equivalence
from the existing affinoid pushout of the actual map on `(P₀,W₀)` along the
actual restriction `W₀ → W`, to the unchanged algebra of `P`.
All pieces may be arbitrary recognized subsets.

## Construction and equations

The existing `inclusionDomain` makes each nested recognized restriction
a full domain representation. Pulling back the target representation
along the actual recognized map gives a full domain over `P₀.algebra`.
The recognized chart equation and the supplied inverse-image equality
identify its locus with the locus of `P.inclusionDomain P₀ hP`.
`Domain.boundedEquivOfLocusEq` constructs the bounded equivalence.

`recognizedNestedPullbackEquiv_comp_leftMap` identifies the comparison
composed with the first pushout leg with the complete original source
restriction. `fullRecognitionPairs_nestedPullback_eq_pushout` identifies
the map on `(P,W)` with the comparison composed with the second pushout
leg. Its proof uses the full recognized restriction square and uniqueness
of bounded maps out of the target domain representation, so it retains
the entire algebra maps, including nonreduced information.

`recognizedNestedPullbackEquiv_chart` proves that every point of `P`,
transported through the comparison and then projected along the first
pushout leg, has precisely its original ambient source point.

## Provenance and scope

This is a derived construction from the Library's full recognition pair
systems, recognized inclusion domains, actual domain base change and
equal-locus bounded equivalences. It extends the construction of
`RecognizedContainedMap` to arbitrary nested recognized pairs by using
`inclusionDomain` directly. No external theorem is asserted here.

The construction preserves independent field, ambient-space and
atlas-index universes `u/v/w`. It uses no Hausdorff assumption on the
ambient spaces and no strict-radius or nontrivial-valuation hypothesis.
Neither finiteness, algebraic flatness, ordinary tensor comparison
bijectivity nor pointwise étaleness is assumed or concluded.

## Conditional pointwise transport support

The accompanying modules `FlatTargetDescent`, `TensorStalkReflection`,
`AffinoidPointwiseReflection`, `PointwiseEtaleBoundedEquiv`,
`RecognizedNestedEtale` and `FinitePiecesEtaleAllPiecesReduction` provide
the algebraic reflection and the complete conditional finite-to-all
assembly. Each module's paired Markdown states its exact hypotheses and
implemented proof. The last two explicitly assume full-domain flatness
and finite ordinary tensor comparison. This construction candidate does
not supply either of those substantial algebraic inputs and does not
claim the unconditional task target.
