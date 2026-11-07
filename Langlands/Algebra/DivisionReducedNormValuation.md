# Canonical reduced-norm valuation

Let `K` be a complete nontrivially normed field with ultrametric distance,
and let `D` be a finite-dimensional central division algebra over `K`.
Both carriers are in an arbitrary common universe. The definition
`Langlands.CentralDivision.reducedNormValuation K D` is an actual
`Valuation D NNReal`, on the original possibly noncommutative division ring,
with value

```
v(x) = ‖reducedNorm K D K (1 ⊗ₜ[K] x)‖₊.
```

Here `reducedNorm` is the canonical reduced norm already constructed in
`Langlands.Algebra.ReducedNorm`; the tensor inclusion identifies the original
algebra with its scalar extension from `K` to itself. No norm on `D` is supplied.
There is no characteristic or separability hypothesis.

The multiplicative valuation convention gives `v(0) = 0`, `v(1) = 1`,
`v(x*y) = v(x)*v(y)`, and `v(x+y) ≤ max (v(x)) (v(y))`.
Its restriction to the central scalars is

```
v(algebraMap K D a) = ‖a‖₊ ^ reducedDegree K D.
```

In particular, this definition uses the reduced norm without extracting a
root to make the restriction equal to the given absolute value.

## Implemented proofs

`regularNorm_eq_reducedNorm_pow` first transfers the regular determinant norm
across `Algebra.TensorProduct.lid K D`. The existing comparison
`Langlands.CentralSimple.norm_eq_reducedNorm_pow` then identifies it with the
`reducedDegree K D` power of the canonical reduced norm evaluated at
`1 ⊗ₜ[K] x`.

`norm_reducedNorm_add_le` raises the desired nonnegative-real inequality
to this positive integer power. The regular-norm comparison turns the left
side into `‖Algebra.norm K (x+y)‖` and the powered right side into
`max ‖Algebra.norm K x‖ ‖Algebra.norm K y‖`. The ultrametric inequality
`Langlands.CentralDivision.norm_regularNorm_add_le` supplies the comparison.
Strict monotonicity of a positive power on nonnegative reals gives the original
inequality. This cancellation takes place in ordered real values.

The valuation's zero, one, and product laws follow from the tensor inclusion,
the multiplicative canonical norm, and the base absolute value. The proved
real-valued ultrametric inequality is then cast to `NNReal`.
`reducedNormValuation_algebraMap` rewrites a central scalar in the tensor
product as `a ⊗ₜ[K] 1` and applies `reducedNorm_scalar`.

Finally, `regularNormValuation_eq_reducedNormValuation_pow` states the pointwise
comparison

```
regularNormValuation K D x =
  reducedNormValuation K D x ^ reducedDegree K D.
```

It follows directly from the algebraic regular/reduced norm identity and
multiplicativity of the base norm.

## Provenance and scope

This is an internal consequence of the existing canonical-norm comparison and
regular-norm valuation modules, composed with the scalar-extension equivalence
and ordered-power facts from Mathlib. The preceding regular-norm valuation
module contains the field-extension and one-generator-field arguments needed
for its triangle inequality. This module adds no structural hypothesis to
that argument beyond centrality, which is needed for the canonical reduced
norm.

This contribution constructs the stated valuation and its normalization.
Discreteness, a description of the residue division algebra, unramified cyclic
maximal subfields, local SK1, and the general local Kneser–Tits proposition
remain separate obligations.
