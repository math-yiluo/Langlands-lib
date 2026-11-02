# Product points in the actual base-changed local models

Author: Worker 208.

For a commutative ring `C`, any family of commutative `C`-algebras `R i`, and
an actual scheme `X` over `Spec C`, `localProductPointMap C R X` maps an
actual `C`-morphism `Spec (∀ i, R i) → X` to a family of actual `R i`-morphisms
from `Spec (R i)` to `X ×[Spec C] Spec (R i)`.

The construction restricts the point along the spectrum of the coordinate
projection and then applies the existing pullback-adjunction point equivalence.
`localFactorPointEquiv` is the factorwise equivalence from the original
relative points to those of the actual base-changed models. Its inverse
forgets each base change by composition with the first pullback projection.
`localFactorPointEquiv_symm_localProductPointMap` proves that this inverse
recovers exactly the existing `productPointMap`.

`localProductPointMap_left_fst` identifies the underlying local point after
projection to `X` with `Spec (Pi.evalRingHom R i) ≫ p.left`.
`localProductPointMap_left_snd` gives the second projection as the local test
spectrum's structure map. These two identities identify the usual pullback
lift. `localProductPointMap_natural` proves that the construction commutes with
morphisms over `Spec C`, using the actual pullback functor at each factor.

This is derived geometric infrastructure for Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed p.6,
Theorem 3.6 and formula (3.6.1), and printed p.7, formula (3.6.2). Registered
source: `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The source's local targets are points of the base changes to the local value
rings. This construction makes that change of base explicit for an arbitrary
product family, rather than identifying relative morphisms over different
bases by notation.

All rings, index types and schemes lie in an arbitrary common universe `u`.
There are no topology, finite-type, affineness, quasi-compactness,
quasi-separatedness or local-ring hypotheses in this construction. In
particular, this file makes no bijectivity assertion. The separate
injectivity and surjectivity conditions on the product map, its affine
topology comparison, the arithmetic realization of the factors as `F_v` and
`O_v`, the `S`-level adelic ring, and the transition maps remain separate
obligations. An abstract product family alone is not the arithmetic theorem.
