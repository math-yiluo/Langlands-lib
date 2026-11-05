# Finite-model descent from geometric Frobenius invariance

Authors: Worker 1442.

This internal supporting construction descends a specified finite split-torus
model when the original subgroup over an algebraic extension is invariant
under Frobenius on every relative test scheme. All fields and schemes use an
arbitrary common universe `u`.

Let `k` be a finite field with a `Fintype` instance, let `Ω/k` be algebraic,
and let `G` be a group scheme over `k`. Fix a commutative group scheme `T`
over `Ω`, an actual homomorphism `i : T → G_Ω`, and finite-model data
`D : TorusFiniteModel.Model k Ω i`. The latter records a finite intermediate
field `E/k`, a closed split-torus inclusion `D.inclusion` into `G_E`, and
an exact recovery of `i` after extending to `Ω` through the canonical tower
comparison. No commutativity hypothesis is imposed on `G`.

`Model.range_baseChange_comap_comparison` identifies the all-test range of
`i` with the range of the finite model after extension and inverse image
along the actual ambient comparison. It follows directly from the finite
model's recovery equation, invariance of range under a source isomorphism,
and cancellation of an ambient isomorphism.

`Model.frobeniusInvariant` assumes that `SubgroupFunctor.galoisTransport`
for the cardinal-`k` Frobenius fixes `range i`. It proves that the same
Frobenius transport over `E` fixes `range D.inclusion`. To compare transports,
a private tower lemma checks their points after projection to the original
group over `k`. An identity-underlying isomorphism identifies the changed
base structures on each test scheme; precomposition with it and its inverse
preserves subgroup membership. The Frobenius square for `E → Ω` follows
from compatibility of the cardinal-`k` power map with the algebra map.
The canonical finite-stage comparison has the required projection law.
Exact recovery then equates the two extended subgroup functors. Cancelling
the ambient comparison and applying fpqc reflection of represented ranges
proves the equality over `E`. Closedness supplies the two representing
monomorphisms used in reflection.

`Model.descentOfFrobenius` additionally assumes that `G` is affine over `k`.
It returns actual data `TorusDescent D.inclusion`: a commutative torus over
`k`, a closed inclusion into `G`, a recovery isomorphism after extension to
`E`, and an equality recovering the specified finite-model inclusion.
Finite dimensionality of `E/k` makes `E` finite as a type. Finite-field
Frobenius generation therefore gives invariance under every `k`-automorphism
of `E`. The existing finite-Galois closed-subgroup construction gives full
overlap invariance, and `IsTorus.descentOfOverlapRangeEq` constructs the
actual descended torus and its comparison equation.

The provenance is internal: this module combines the actual finite model
from `Torus.FiniteModel`, canonical transport and finite-field Frobenius
generation from `Descent.GaloisSubgroupTransport`, all-test effective Galois
descent from `Descent.GaloisClosedSubgroups`, and fpqc represented-range
reflection from `SubgroupFunctor.FpqcDescent`. The tower compatibility is
proved here using the published point equivalences and actual projection
laws. No external numbered theorem is asserted.

The construction starts from an existing model and assumes geometric
Frobenius invariance. It does not construct an invariant maximal torus, prove
the host finite-field existence statement, or supply a direct recovery
isomorphism over `Ω` for the output. Composing the two recovery data through
the field tower remains a consumer step. The existing maximality lemmas for
`Model` and `TorusDescent` apply separately to their respective recovery
equations; this module does not use forward preservation of maximal tori.
