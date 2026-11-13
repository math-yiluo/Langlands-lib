# Integral descent data on a supplied finite unramified model

This internal construction supplies actual Čech descent data on the actual
finite unramified integer cover. The base F is a nonarchimedean local field
at arbitrary universe `u`, and E is an intermediate field of its separable
closure contained in the inertia fixed field. Containment is carried by the
instance `Fact (E ≤ inertiaFixedField F)` solely so that the specified
coefficient algebra structures can be inferred. These structures use the
actual field inclusion and `spectralIntegerInclusion`; both scalar towers
are proved, and flatness and surjectivity of the integer coefficient map are
provided by `spectralIntegerMap_fpqc`.

The input N is an actual integral model over `extensionIntegers F E` of the
base change to E of a specified F-group G. The input P is a smooth integral
model of the base change of G to the inertia fixed field, over its actual
integers. An actual compatible recovery isomorphism from the coefficient
extension of N to P is supplied. Its generic map is the canonical tower
comparison `finiteInertiaGenericIso`, built from the actual inclusions
F to E to the inertia fixed field. The construction assumes the fixed-ring
property `HasSmoothHomExtension` over the inertia integers and P's original
integral-point image is stable under every F-automorphism of the inertia
fixed field. It assumes no stability statement for the integral points of N.

For each automorphism σ of E over F, `finiteIntegralSemilinearIso` constructs
an actual compatible isomorphism from the σ-twist of N to N. It chooses an
extension of σ to the inertia fixed field, constructs the integral upstairs
semilinear isomorphism from the supplied extension property and P's point
stability, and applies `semilinearIsoFromCoefficients`. The four required
coefficient/generic squares are the proved actual lift squares. The exact
generic compatibility of recovery with the canonical semilinear maps is
`finiteInertiaGenericIso_semilinear`, deduced from canonical tower
semilinearity. `finiteIntegralSemilinearIso_generic` retains the precise
finite generic law.

For `finiteIntegralDatum`, E over F is additionally finite-dimensional,
Galois, and supplied with the published arithmetic unramifiedness property.
The construction uses the published normalized components of the actual
integer overlap and its transported finite Galois index multiplication.
`finiteFieldBaseAut_comp` proves that the field maps have the same
multiplication law. The canonical finite generic semilinear maps obey the
tower law, so generic rigidity proves integral coherence and the finite
component constructor assembles the actual Čech datum.
`pullIso_finiteIntegralDatum` recovers exactly the constructed integral
semilinear isomorphisms with the standard normalized orientation. No
multiplicative compatibility of the chosen upstairs lifts is used.

This is an internal consequence of the actual automorphism lift, coefficient
isomorphism descent, generic rigidity, and published finite unramified
component cover. It retains existence of the finite model and its exact
recovery, and the smooth extension property, as inputs. It constructs no
effective solution of the datum or final descended model and does not prove
KP Fact 2.10.16.
