# Strict Lie-dimension decrease for smooth quotients killing Gm

This internal helper supplies the dimension decrease needed to apply induction
to a smooth affine quotient in the Borel normalizer argument. It does not
construct such a quotient or prove the Borel normalizer theorem.

`gmInfinitesimalUnit` is the unit `1 + ε` of the actual dual-number ring, with
inverse `1 - ε`. `gmTangent` uses the existing affine-points equivalence for Gm
to make this an actual point of the kernel of reduction to the ground ring.
Reduction sends this unit to one. It differs from the identity whenever the
ground ring is nontrivial, since its epsilon coefficient is one.

`dimension_lt_of_smooth_of_kernel` takes affine locally finite type groups over
an arbitrary field, a smooth homomorphism between them, and a nonzero element
of the actual Lie kernel killed by its linear differential. The existing
smooth-differential theorem supplies surjectivity. Finite dimensionality bounds
the target dimension by the source dimension; equality would force the
differential to be injective and contradict the supplied nonzero kernel vector.

`dimension_lt_of_smooth_kills_gm` applies this argument when the homomorphism
kills an actual monomorphic Gm inclusion. Monicity makes its differential
injective, so the image of `gmTangent` is nonzero. The equality of the underlying
composite with the constant identity morphism makes that image lie in the
differential kernel.
The result is strict decrease of `Lie.dimension`. No connectedness, algebraic
closedness, centrality, surjectivity on ordinary points, or smoothness of the
group structure morphisms is required beyond the explicit hypotheses.

The constructions and proofs are derived from the published Gm point
equivalence, naturality under affine coefficient changes, the actual Lie-kernel
linear target maps, finite dimensionality, and smooth lifting. There is no
additional external structural input.
