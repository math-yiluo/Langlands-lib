# The unitary group scheme as a multiplier kernel

Author: Worker 57.

This module constructs the unitary group scheme as the kernel of the previously
constructed similitude multiplier. It proves that its points are exactly the
existing algebraic unitary elements over relative global sections, with the
expected inclusion and coefficient-change formulas. The inclusion is a closed
immersion, so the unitary group scheme is affine. The construction specializes
to the rational involution of the existing central simple CM algebra datum.

## Internal provenance and scope

This is an internal consequence of `RationalGroupScheme`, the existing
`AlgebraInvolution.unitaryEquivKernel` in `Similitude`, and the categorical
kernel and point comparison in `AbelianScheme.Kernel`. The latter constructs
an actual pullback of group schemes, not a record assuming a kernel exists.
The point comparison below uses the previously proved multiplier formula.
No external representability, smoothness or reductivity theorem is asserted.
The original involution and arithmetic conventions are unchanged from the
imported `Similitude` and `CMData` pairs.

The generic scope is the same as `RationalGroupScheme`: a commutative base
ring, a possibly noncommutative algebra, an algebra involution and a finite
basis, with the base, algebra and basis index in a common universe. Test
schemes are arbitrary schemes over `Spec R` in that universe. Neither
reducedness nor affineness of the test schemes is assumed. The rational
specialization uses small types for the fields and algebra, with the
compatible rational scalar structures documented in `RationalGroupScheme`.

This contribution establishes the kernel, its affine geometry, its natural
point formula and its rational specialization. It does not establish
smoothness, reductivity, connectedness, Harris signature or local inner-form
conditions, PEL moduli representability, canonical models, scheme levels or
coefficient descent. The broader task retains these obligations.

## The actual kernel and its points

In `AlgebraInvolution.SchemeModel`, `unitaryGroupScheme b σ` is
`GroupScheme.kernel (multiplier b σ)`. The reused construction is a pullback
of the multiplier homomorphism and the unit map from the trivial group scheme.
`unitaryInclusion b σ` is its projection to the actual similitude group scheme.
Thus its group law, inclusion and underlying scheme are categorical
constructions from existing group schemes.

The private `kernelComparison b σ T` identifies two groups: the kernel of
postcomposition by the multiplier on scheme points, and the kernel of the
algebraic multiplier after recovering the similitude over the relative
algebra of global sections. Its forward map applies `pointsEquiv` and its
inverse applies that equivalence in reverse. Membership of the forward
image follows from `multiplier_points`, since the original scheme point
maps to the identity. For the inverse map the proof applies the injective
`Gm.pointsEquiv`, uses the same multiplier formula and cancels the point
equivalence. The inverse laws and multiplication law are inherited from
`pointsEquiv`, using subtype extensionality.

`unitaryPointsEquiv b σ T` composes the existing kernel point equivalence,
this kernel comparison, and the inverse of `unitaryEquivKernel` for the
scalar-extended involution. Its target is exactly
`(σ.baseChange ((algΓ (CommRingCat.of R)).obj T).unop).unitary`, with the
already defined subgroup law. Those elements are invertible algebra elements
`g` satisfying `g σ(g) = 1`. The scalar action on global sections comes from
the structural map of `T`, as in the similitude point comparison.

`unitaryPointsEquiv_val` is a definitional equality: the recovered unit is the
first coordinate of the similitude recovered after postcomposing with the
kernel inclusion. `unitaryInclusion_points` states the stronger equality in
the similitude group: applying the algebraic `unitaryInclusion`, which records
multiplier one, gives that recovered included point. Its proof projects the
inverse law of `unitaryEquivKernel` to the ambient similitude group.

For `a : T' ⟶ T`, `unitaryPointsEquiv_naturality` identifies the underlying unit
of the restricted point with `Units.map` of the original tensor coefficient
homomorphism induced by `((algΓ R).map a).unop.hom`. The proof rewrites the
unit-coordinate formula, associates the scheme composites, and applies the
previously established naturality of similitude points. The remaining
identity is definitional. This is an equality of ambient algebra units;
both sides come from the already constructed unitary point comparison, so
it specifies the restriction on the entire unitary subgroup.

## Closed immersion and affineness

`unitaryInclusion_isClosedImmersion` derives separatedness of the target
`Gm` structural morphism. Its underlying scheme is the base change of the
spectrum of the integral Laurent polynomial ring. The original spectrum
morphism is separated, and separatedness is preserved by base change. The
existing kernel theorem then makes the inclusion a closed immersion: the
kernel square is the base change of the target's closed unit section.

`unitaryGroupScheme_isAffine` follows because a closed immersion is an affine
morphism and the similitude scheme is already affine. No separatedness or
affineness hypothesis is added to the involution or its test schemes.

## Rational specialization

`CentralSimpleUnitaryData.rationalUnitaryGroupScheme` specializes the generic
kernel to the rational basis derived from `D.finite` and the existing
rational restriction of its second-kind involution.
`rationalUnitaryInclusion` is the resulting morphism to
`D.rationalGroupScheme`. `rationalUnitaryPointsEquiv` gives its point
comparison on every small scheme over `Spec ℚ`, with target the unitary
subgroup of the actual rational scalar extension to relative global sections.
These declarations are specializations of the generic constructions and
preserve all their inclusion, restriction and geometric properties.
