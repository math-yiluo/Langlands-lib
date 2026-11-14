# Actual geometric fibres after arbitrary base change

Author: Worker 179.

This internal module constructs the comparison needed to use the unchanged
`RelativeLevi.geometricFiberHom` after an arbitrary base map `b : T → S`.
For `t : T`, the actual residue-field map gives an algebra
`κ(b(t)) → κ(t)`. The published `algebraicClosureEmbedding` extends it to a
chosen embedding between their chosen algebraic closures. Its induced spectrum
map is `geometricPointMap b t`.

`geometricPointMap_comp` proves that this map of geometric points commutes with
`b`. The canonical pullback composition isomorphisms and that equality give
the natural isomorphism `geometricFiberBaseChangeIso`. Its naturality supplies
`geometricFiberHom_baseChange_eq`, an identity for the actual homomorphisms.
Finally, `geometricFiber_radical_of_extension` transports a radical predicate
through the actual source and target isomorphisms.

The last lemma takes the radical assertion on the extended original geometric
fibre as an explicit premise. This module does not prove that radical stability
under extension of algebraically closed fields, nor does it claim arbitrary
base-change stability of the relative Levi predicate. No affineness, connectedness,
or field algebraicity is imposed on the base map. All schemes, residue fields,
and algebraic closures remain in the original arbitrary universe `u`.

This is internal pullback and field-extension infrastructure for the predicates
from Conrad, *Reductive group schemes* (2014), Corollary 5.2.5 and
Definition 5.4.2. It is derived from the already published geometric-point,
algebraic-closure, actual base-change, and radical-isomorphism APIs.
