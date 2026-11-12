# Homeomorphisms from continuous comparisons of stages

Author: Worker 113.

This internal topological construction supports comparison of adelic point
topologies defined as final topologies of arithmetic stages. It is derived
from Mathlib's universal properties `continuous_iSup_dom` and
`continuous_coinduced_dom`, with no additional source assertion.

Let `p i : P i → A` and `q j : Q j → B` be families of maps from
topological spaces to sets. Endow `A` and `B` with the suprema of the
coinduced topologies. `HasContinuousStageLifts p q f` means that, for
every source stage `i`, there is a target stage `j` and a continuous map
`g : P i → Q j` such that `f (p i x) = q j (g x)` for every `x`.

`HasContinuousStageLifts.continuous` proves continuity of `f` for these
final topologies. On each source stage its composite is `q j ∘ g`.
The structural map `q j` is continuous by definition of the final
topology, so this composite is continuous. The universal property of
the source final topology gives the result.

`homeomorphOfStageLifts p q e h h'` applies this argument to a set
equivalence `e` and its inverse. Its underlying equivalence is exactly
`e`, as verified by the application lemma. There are no injectivity,
surjectivity, directedness or cofinality requirements on the stage
families: the two directions of compatible lifts are explicit inputs.
This module constructs no stage lifts itself.
