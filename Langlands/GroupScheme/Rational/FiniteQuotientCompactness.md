# Compactness from a compact subgroup and a finite schematic quotient

Author: Worker 1567.

This is internal infrastructure for the full scheme-center quotient compactness
proof. It retains finite scheme data in every characteristic and makes no
surjectivity claim for the rational points of a quotient morphism.

`compactSpace_of_finite_image_of_isCompact_ker` applies to a group with
continuous multiplication and a homomorphism with finite image. It chooses one
representative for each attained value, expresses the full group as a finite
union of translates of the compact kernel, and uses continuity of translation.
The codomain requires no topology, and the homomorphism need not be surjective.

`affineCoordinate_finite_of_isFinite` transports finiteness of an actual scheme
structure morphism through the canonical affine global-sections isomorphism.
`finite_ringPoint_of_isFinite` then identifies actual points in a field
extension with algebra homomorphisms out of the finite-dimensional coordinate
algebra. Mathlib's `Finite.algHom` proves finiteness by linear independence of
these algebra homomorphisms; it does not require a reduced source algebra.
`finite_rationalPoint_of_isFinite` transports this finite carrier to the actual
identity-test convention used by `GroupScheme.rationalPoints`.

These are derived results from the existing canonical point equivalences,
Mathlib's finite-morphism characterization, linear independence of algebra
homomorphisms, and finite unions of compact sets. They do not assert that the
full center quotient has been constructed, or that its largest torus is
anisotropic or compact.

`compactSpace_rationalPoints_of_finite_quotient` combines these results for
actual group schemes over a topological field. Its ambient group is affine and
locally of finite type, so the canonical identity-test topology makes its
points a topological group. The supplied subgroup source is affine with compact
canonical points. The supplied morphism to a finite group scheme has exactly
the subgroup's all-test range as its kernel. The theorem evaluates that equality
on the identity test, identifies the point kernel with the continuous image of
the compact subgroup source, and applies the finite-image theorem. It does not
need a closed immersion, a surjective schematic morphism, or any topology on the
finite target. `compactSpace_rationalPoints_of_finite_fppf_quotient` specializes
the exact-kernel input to an explicit represented fppf quotient. Fppf
surjectivity is not promoted to rational-point surjectivity.
