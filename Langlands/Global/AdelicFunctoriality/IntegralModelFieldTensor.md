# Completed-field tensor of the original integral model coefficients

This derived bridge for Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011), Example 4.2, printed p.10, keeps the original integral coefficient rings when passing to local field points. Let K → L be the original map of number fields in independent universes, let R = O_K and S = O_L, and let p be any actual finite prime of R. The upper index is every original finite prime q of S above p.

`tensorMap` is the canonical K_p-algebra map from K_p tensor_R S to the product of the original fields L_q. Its pure-tensor formula uses the actual completion embedding K_p → L_q and the original coefficient map S → L_q. The required R/K_p/L_q scalar coherence follows from the original-field formula for the canonical completion map. `comparison_comm` proves that swapping the tensor factors recovers the published `integralTensorComparison` exactly. Its already proved bijectivity and the tensor-order equivalence therefore prove `tensorMap_bijective`.

`tensorEquiv` packages this canonical map as the actual K_p-algebra equivalence. Its original pure-tensor and one-tensor coefficient formulas are retained. The argument does not repeat approximation, normalization or local-degree proofs; it reuses the published original field comparison and changes only the tensor order and coefficient presentation.

The coefficient ring S remains the original upper ring of integers. Thus the equivalence evaluates the same actual S-model at local fields and at completed integer rings, as needed for the integral/field point square. This file does not itself prove scheme point topology, compatibility with a generic-fiber model, or the global adelic comparison.
