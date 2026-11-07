# Constructed rank-one arithmetic epsilon data

Worker 1555 derives this internal construction from the published p-adic
Fourier duality, Gauss nonvanishing and abelian Laurent epsilon formula,
and the exact full rank-one arithmetic spectral certificate. No new
original-literature assertion is introduced.

`existsUnique_localSelfDualMeasure` specializes the published
`LocalFactors.padicFourierDuality` to the actual canonical topology of `F`
and the given continuous nontrivial unitary additive character. It extracts
existence and uniqueness for the unchanged intrinsic self-duality predicate.
`localSelfDualHaar` chooses that actual regular additive Haar measure from
this proved existence. Its self-duality and equality with every supplied
self-dual measure follow from the same existence and uniqueness theorem.
No measure existence is assumed.

`baseGeometricFrobenius`, reused from
[BaseLocalEuler](BaseLocalEuler.md), constructs a bottom-field Frobenius from the
existing actual `localGeometricFrobenius F`. The bottom intermediate field
has the whole Galois group as its fixing subgroup, so its pullback contains
this element. Its norm is the inverse base residue cardinality. The
canonical algebra equivalence from the bottom field to `F` preserves residue
cardinality, proving the required norm identity for the bottom field.

`abelianSpectralEpsilon_ne_zero` specializes the published
`PadicAbelian.epsilonAt_ne_zero` at the actual multiplicative and additive
conductors. Their least and greatest characterizations give the exact
conductor premises of that theorem. This applies at every complex parameter
and every actual regular additive Haar measure.

`rankOneArithmeticEpsilonCoefficient` is the complex unit whose value is the
existing unshifted Deligne constant at the chosen unique self-dual measure.
Its nonzero certificate is the preceding result at parameter zero.
`abelianSpectralEpsilon_eq_rankOneMonomial` first identifies an arbitrary
supplied self-dual measure with that chosen measure, then uses the existing
all-parameter monomial formula. The exponent is precisely
`multiplicativeConductor chi + additiveConductor psi`. The existing abelian
spectral variable agrees with the correspondence's `spectralPoint` by the
positive real logarithm formula for complex powers, so the monomial has the
unchanged convention `c * q^(-s)^m`.

`isArithmeticPairEpsilonFactor_rankOne_constructed` provides the complete
arithmetic epsilon certificate for the two actual rank-one Weil quotient
classes. Its coefficient is the constructed unit for the product of the
original quasicharacters, and its exponent is that product's actual
multiplicative conductor plus the original additive conductor. The exact
spectral-certificate equivalence supplies all original restriction and
universal clauses; proved self-dual measure existence and the constructed
bottom Frobenius supply its two remaining existence clauses. Uniqueness of
the self-dual measure gives the required identity for every such measure.

Every prime and finite p-adic field is retained. The field, parameter-carrier
and supplied-system universes remain independent. Standalone reciprocity,
common-closure reciprocity, compatibility between them and a validated
local-constant system are still explicit inputs. This unit constructs no
such family or system and proves no analytic JPSS epsilon comparison or
closed supercuspidal correspondence.
