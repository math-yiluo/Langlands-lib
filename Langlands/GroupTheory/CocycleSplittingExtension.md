# The concrete cocycle splitting representation

This internal construction associates a representation to a normalized
multiplicative two-cocycle `c` for a finite group acting on a commutative
group `A`. Its additive carrier is `Additive A × Ideal G`, over the
lifted integral scalars used by the actual coefficient representation.

For an augmentation vector `f`, the correction term is the sum of
`f x` times the additive form of `c (g, x⁻¹)`. The action sends `(a,f)`
to the pair consisting of `g a` plus this correction and the right
translate of `f`. The cocycle equation and the zero coordinate sum of
`f` prove the multiplication law for this action. These are derived
auxiliary definitions for transfer reciprocity.

The inclusion `a ↦ (a,0)` and projection `(a,f) ↦ f` give the
short exact sequence from the original coefficient representation through
the splitting representation to the augmentation ideal. The exactness
proof uses the displayed coordinates. The sequence splits over the scalar
ring by projection onto the first coordinate and inclusion of the second.
The augmentation sequence also has a scalar splitting, with section
`r ↦ r • delta G 1`.
