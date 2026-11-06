# Harris CM representatives with normalized full integral Tate images

Author: Worker 344.

This internal adapter combines exact Tate lattice realization with the
original Harris CM polarized model construction. It works over an
existing connected admissible CM test base and at an original Harris
level whose image under the original Hodge level functor preserves the
fixed Harris integral source span. The geometric point has an
algebraically closed field. Existence from the generic realization
target also retains its characteristic-zero field hypothesis.

`TateNormalizedCMRepresentative` extends the existing
`IntegralCMRepresentative`. It retains the original polarized object and
fixed level, the original normalized CM determinant and geometric
dimension condition, and an actual action of the original integral
order on that same abelian scheme. Its additional field is exactly the
existing `HarrisIntegralLevelCondition`, which identifies the fixed
integral source span with the full actual integral Tate image through a
frame in that original level orbit.

For `cmIsogenyModel_level_normalized`, the inputs include an original
representative, an actual abelian scheme `B` over the same base, an
exact rational isomorphism `e : B → A`, and the assertion that the full
integral Tate image of `B` under `e.hom` is exactly the lattice carried
by the original level orbit. The published supplied-model construction
equips `B` with the conjugate faithful rational action and an actual
compatible polarization, and retains `e.inv` as the exact comparison
from the original representative to the model. Its multiplier is the
positive square of the chosen forward integral denominator. The
published normalization-under-isogeny equivalence then shows that the
original level transported by that exact comparison is normalized.

`cmTateNormalizedIsogenyRepresentative` assembles that normalized
transported level with the same polarized model. The existing
supplied-model equivalence transports the original CM determinant and
dimension condition. The normalized-level integral reflection
construction recovers an actual unital action of the original Harris
order on `B`, agreeing exactly with the model's rational action. The
choice of integral action changes no other data.

`cmTateNormalizedIsogenyRepresentative_class` proves that forgetting
this normalized integral representative yields exactly the original
CM class. It applies the original class-equality criterion to the
unchanged comparison, its proved multiplier equation and the literal
transported level. It does not replace rational-isogeny equivalence by
actual isomorphism equivalence.

`exists_tateNormalizedCMRepresentative` retains two explicit
prerequisites: a proof of the published generic
`CommensurableInvariantLatticeRealizationStatement` and its finite-set
source fibre-affineness hypothesis on the original abelian scheme.
The original fixed orbit gives actual monodromy invariance of its
carried lattice. The published compact-open integer-bound theorem
supplies the two commensurability inclusions with one positive integer.
Applying the generic target then supplies `B`, `e` and the exact image
equality needed above. Thus the theorem gives a normalized integral
representative of the same original CM class under those explicit
prerequisites.

The provenance is internal and derived from the named published
constructions. This file does not prove generic lattice realization or
source fibre-affineness, remove the integral source-stabilizer
hypothesis, construct a representing scheme, establish its
admissibility or prove division-case representability. The supplied
model assembly needs no generic existence hypothesis; only the final
existence theorem assumes the generic realization target.
