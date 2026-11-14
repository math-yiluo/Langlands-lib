# Explicit opposite-root commutator factors in SL₂

This internal calculation uses the Library's actual determinant-one
transvections and `SpecialLinear.Root.contractingMatrix`. Over any field `E`,
write `upper(a) = [[1,a],[0,1]]`, `lower(b) = [[1,0],[b,1]]` and
`diagonal(t) = diag(t,t⁻¹)`. The function `oppositeProductPivot a b` is
`1+a*b`, the leading entry of `upper(a)*lower(b)`.

For a nonzero pivot `t`, `upper_mul_lower_factorization` constructs the
lower, diagonal and upper factors with coordinates `b/t`, `t`, `a/t`.
Its proof checks all four matrix entries and clears the nonzero denominator.
The result `oppositeCommutator_factorization` multiplies this equality on the
left by `lower(b)⁻¹` and on the right by `upper(a)⁻¹`. The additive law
for transvections gives the outer coordinates `b/t-b` and `a/t-a`.
The commutator convention is exactly
`lower(b)⁻¹ * upper(a) * lower(b) * upper(a)⁻¹`.

For any additive valuation `omega : E → WithTop ℝ`, the pivot deviation
satisfies `omega(t-1) = omega(a)+omega(b)`, including at zero parameters.
If this sum is a finite positive real number `r`, the pivot is nonzero:
otherwise its deviation is `-1`, of value zero.
`exists_oppositeCommutator_factorization_of_value_sum` then constructs the
actual three factors and gives the exact equality `omega(t-1) = r`.
These proofs use only multiplication of the additive valuation and its
values at `1` and `-1`.

The module is derived matrix algebra over the existing Library definitions.
It is the SL₂ calculation needed by the local coroot-component argument.
It does not assert existence of coordinates for an arbitrary group, identify
a building valuation with these coordinates, or supply a character
congruence for a restriction-of-scalars torus.
