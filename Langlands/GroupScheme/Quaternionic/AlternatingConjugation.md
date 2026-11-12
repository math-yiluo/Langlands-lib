# Conjugation obtained from an alternating quaternionic unit

Authors: Worker 124.

This internal construction starts with the published involution of the
first kind `σ` on a division algebra `D` over a field `K`. For an
invertible anti-selfadjoint element `ℓ`, `alternatingTwist` is the actual
involution `a ↦ ℓ σ(a) ℓ⁻¹`. Its inverse, linearity and
anti-multiplicativity laws follow directly from the published involution
and unit inverse laws. Alternating elements are anti-selfadjoint in every
characteristic.

Assume that `σ.alternatingSubspace` has `K`-dimension one, and that `ℓ`
is an invertible member of that subspace. The sandwich
`a ℓ σ(a)` belongs to the same subspace: if `ℓ=b−σ(b)`, it equals
`a b σ(a)−σ(a b σ(a))`. Hence it is a scalar multiple of `ℓ`.
The actual function `alternatingNorm` chooses this scalar. The lemma
`alternatingNorm_spec` identifies its scalar image with the conjugate
product `a·alternatingTwist(a)`.

The function `alternatingTrace` is
`alternatingNorm(1+a)−1−alternatingNorm(a)`. Expanding the conjugate
products identifies its scalar image with `a+alternatingTwist(a)`.
These constructions work for independent universes of `K` and `D`.

When `K` and `D` have a common arbitrary universe and `D` is a
finite-dimensional central division algebra of reduced degree two,
`alternatingNorm_eq_reducedNorm` proves that this scalar is the published
unconditional reduced norm of `1 ⊗ a`. In particular,
`reducedNorm_sandwich_alternating` proves the actual identity
`a ℓ σ(a) = Nrd(a) ℓ`.

The reduced Cayley–Hamilton and degree-two coefficient lemmas are reused
from [ReducedCharpolyDivision](../../Algebra/ReducedCharpolyDivision.md).
The Cayley–Hamilton argument uses the published equality between the regular characteristic polynomial
and the positive reduced-degree power of the reduced characteristic
polynomial. The regular multiplication matrix satisfies Cayley–Hamilton,
its algebra representation is injective, and a positive power of a
division-algebra element is zero only when the element itself is zero.
In reduced degree two, the constant coefficient is the reduced norm,
by evaluating at zero and using the scalar norm of `−1`. Expanding the
monic degree-two polynomial gives the explicit quadratic relation for `a`.

For scalar `a`, the norm identity follows from the scalar norm formula.
For nonscalar `a`, subtracting the relation given by the scalar trace and
conjugate product from reduced Cayley–Hamilton yields
`(c₁+t)a = n−c₀`, with all coefficients in `K`. A nonzero coefficient
`c₁+t` would express `a` as a scalar, a contradiction. Thus that
coefficient and then `n−c₀` vanish, giving equality of the two norms.
There is no characteristic restriction or division by two.

The one-dimensionality of the alternating space, the existence of a
chosen invertible generator and the reduced-degree-two hypothesis are
explicit premises here. This pair does not infer them from the
quaternionic target's dimension assumptions. It does not assert a
spin-group comparison, generation theorem or extension of the norm
identity to all scalar algebras.
