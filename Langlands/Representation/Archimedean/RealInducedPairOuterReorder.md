# Reordering the mixed outer target at a linked pair

This internal derived module concerns a pair of complex character data `d,e` with `IsLinkedAt d e k`. It assumes that the absolute weight `L` of `d` is positive. Let `D` be `outerData d e k`, of weight `P = max(L,M)+k+1`, and let `v = first d` and `x = second e` be the actual endpoint characters.

The module constructs an actual complex linear equivalence

`KFin 4 [character v, induced D, character x] ≃ KFin 4 [induced D, character v, character x]`.

Both directions exactly intertwine the right compact action and all real Lie derivatives. In the reordered list, the two remaining inner endpoint characters are adjacent.

The proof first checks the exact interlacing data for the existing GL3 character-induced equivalence: `0 < L < P` and `(chB D).exponent - v.exponent = -L`. The upper bound follows from the definition of the outer weight. The exponent identity follows from the published linked endpoint equalities, which identify the lower outer endpoint with the lower endpoint of `d`. The chosen GL3 interlaced equivalence is then extended through the final character `x` by `InductionStages.standardEquivInd`. Its forward and inverse intertwining follow from the corresponding induction-in-stages results.

`RealInducedPairOuterReorderStatement` packages this actual GL4 equivalence and exact intertwining in both directions; `realInducedPairOuterReorder` proves it with the construction. The second original weight may be zero. No parity condition is needed for this equivalence. The positive first weight and linked equality remain explicit assumptions.

This module does not identify the image of a restricted outer-tail map, preserve an additional Fourier constraint crossing the GL3 boundary, impose an inner Fourier window, prove nonvanishing of a restricted image, or construct the full two-induced-block filtration. Its provenance is internal: it specializes the proved linked endpoint arithmetic, actual GL3 interlaced equivalence, and exact equivalence extension in stages, without an external classification assertion.
