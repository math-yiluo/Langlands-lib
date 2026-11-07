# Actual semilinear transport of normalized simple-root maps

This is an internal transport construction from the Library's actual
base-change, vector-coordinate and subgroup-functor interfaces. It asserts no
additional result from Steinberg or Borel–Springer. All fields and schemes lie
in the arbitrary universe `u`.

`VectorGroup.baseEndomorphismCoordinates` gives coordinates on the actual
pullback of the standard vector group along any endomorphism of `Spec K`.
It first applies `baseChangePointsEquiv` and then takes ordinary coordinates
on the same test scheme with its structure map changed. Naturality follows
from the two existing naturality laws. The resulting natural coordinate
isomorphisms produce `baseEndomorphismIso` by the existing vector-group
representability comparison. Its forward map preserves these coordinates;
its inverse preserves every global scalar parameter on every scheme test.
No invertibility of the base endomorphism is needed for these constructions.

For maps `b : S → B` and `a : S → S` with `a ≫ b = b`, `semilinearDescentHom`
transports an actual homomorphism into the pullback of a group over `B`.
It composes a supplied source comparison, the actual pullback of the
homomorphism along `a`, and the canonical ambient descent isomorphism.
`descentPoint_comp_descentBaseChangeIso` cancels that last comparison.
`semilinearDescentHom_point` then follows from the ordinary base-change point formula.
`VectorGroup.semilinearDescentHom_scalarPoint` specializes to the standard additive
line and its coordinate-preserving source comparison.

For arbitrary fields `k`, `K`, a `k`-algebra structure on `K`, an affine group
scheme `G` over `k`, and a supplied split pinning `p` of its actual base change,
`SplitPinning.NormalizedRootParametrization.galoisHom` transports the entire
homomorphism of a supplied normalized simple-root parametrization `x`
along `Spec σ`, for any `k`-algebra automorphism `σ` of `K`.
Its source is the standard additive line over `K`, and its target is the
same original base-changed ambient group.

`galoisHom_point` proves the formula on every scheme test and every global
scalar: canonical descent of the transported point equals `x.point` at
that same scalar on the changed-structure test. The explicit equality
`galoisHom_eq_semilinearDescentHom` permits rewriting to the generic construction
without expensive kernel reduction of nested morphism projections.

`galoisHom_range` removes the source isomorphism from the range, applies
`SubgroupFunctor.descentTransport_range`, and uses `x.represents`.
Consequently the range is precisely the canonical transport of the whole
intrinsic root subgroup. `galoisHom_isClosedSubgroup` uses stability of
closed immersions under pullback and composition with isomorphisms.
`galoisHom_represents` combines its resulting monicity with the range
identity, so representation is on all scheme tests.

This contribution does not yet identify the transported subgroup with a
specified simple root, establish its torus character or derivative
normalization, construct a Galois-compatible pinning or root-map family,
or deduce `RootMapsGaloisCompatible`. It establishes neither cross-section
geometry nor the parent quotient theorem, and makes no exceptional
even-type-A section claim.
