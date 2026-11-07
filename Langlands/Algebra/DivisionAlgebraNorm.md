# Normalized determinant norm on a division algebra

Let `K` be a complete nontrivially normed field with ultrametric distance.
Let `D` be a finite-dimensional division `K`-algebra, and put
`N = Module.finrank K D`. The fields and division rings have independent
arbitrary carrier universes, and the characteristic is unrestricted.
No norm or topology on `D` is assumed. The scalar image is central because
`D` is a `K`-algebra; it need not equal the whole center of `D`.

In namespace `Langlands.CentralDivision`, `regularAbsoluteValue K D` is
the actual real-valued absolute value

```
x ↦ ‖Algebra.norm K x‖ ^ (N : ℝ)⁻¹.
```

Here `Algebra.norm K x` is the determinant of `K`-linear left
multiplication by `x`. The positive dimension `N` makes the root well
defined also at zero. This normalization restricts to the given base norm:

```
regularAbsoluteValue K D (algebraMap K D a) = ‖a‖.
```

It is multiplicative, is zero precisely at zero, and satisfies

```
regularAbsoluteValue K D (x + y) ≤
  max (regularAbsoluteValue K D x) (regularAbsoluteValue K D y).
```

Raising it to `N` recovers `‖Algebra.norm K x‖`.
`regularAbsoluteValue_le_iff` and `regularAbsoluteValue_lt_iff` say that
normalization preserves and reflects the non-strict and strict comparisons
of the regular determinant absolute values, respectively.

`regularNormedRing K D` is the normed-ring structure associated to this
absolute value. With that structure installed, `regularNormedAlgebra K D`
makes the original `K`-algebra into a normed algebra. These are explicit
instance-reducible definitions rather than globally installed instances.
They preserve the original ring and algebra operations.

## Implemented proofs and provenance

This is an internal consequence of `regularNormValuation` from
`DivisionNormValuation`, the scalar formula proved there, and Mathlib's
real-power and absolute-value constructions. No additional structural
result is assumed.

Multiplicativity follows from multiplicativity of the regular-norm
valuation and of real powers on nonnegative arguments. The positive real
exponent preserves and reflects zero and order. Applying it to the
regular-norm maximum inequality proves the displayed ultrametric
inequality; the ordinary triangle inequality follows because a maximum of
two nonnegative numbers is bounded by their sum. This supplies all the
absolute-value laws, including nondegeneracy via the original valuation's
zero test.

The scalar formula for `regularNormValuation` is
`‖a‖₊ ^ N`. Taking its positive `N`-th root gives `‖a‖`.
The real-power inverse identities give the dimension-power recovery
formula, and strict monotonicity of a positive real power gives the two
comparison equivalences.

The existing `AbsoluteValue.toNormedRing` construction supplies the metric
and norm. To construct `regularNormedAlgebra`, rewrite `a • x` as
`algebraMap K D a * x`. Multiplicativity and the scalar formula then give
the normed-algebra scalar bound with equality.

## Scope

This module supplies the compatible normed-algebra structure needed for
finite-dimensional topology arguments. It does not assert compactness of
the integer subring, identify a local residue division ring, prove its
finiteness or commutativity, construct a cyclic maximal subfield, or prove
local SK1 or the local Kneser–Tits theorem.
