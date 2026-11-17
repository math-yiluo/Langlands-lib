# Polynomial bounds for real determinant powers

This internal helper for the real-place Whittaker growth estimate is in
namespace `Langlands.Global.RankinSelbergGlobal.RealPlaceRestriction`.
The height `realMatrixHeight g` is the sum of the squared entry norms of
`g` and `g⁻¹`, as defined in `RealLocalWhittakerModel`.

For positive matrix size the proof establishes `2 ≤ realMatrixHeight g`.
It temporarily uses the Frobenius matrix norm: the height is the sum of
the two squared Frobenius norms, and
`1 ≤ ‖g‖ * ‖g⁻¹‖` follows from the product identity and submultiplicativity.
The inequality between the product and the sum of squares gives the
result. This choice of norm is local to that calculation.

Every squared entry norm is bounded by the height, by inclusion in the
finite nonnegative sum. Since the height is at least one, each entry norm
is also bounded by the height. The Library's Leibniz determinant bound
then gives

```text
|det g| ≤ n! * realMatrixHeight g ^ n.
```

Invariance of the height under inversion gives the same bound for
`|det g|⁻¹`.

`exists_det_rpow_le_realMatrixHeight` proves polynomial growth for every
real exponent `β`, including negative exponents. Put
`k = ceil(|β|)` as a natural number and
`B = n! * realMatrixHeight g ^ n`. The two determinant bounds imply
`|log |det g|| ≤ log B`. Thus
`|det g|^β ≤ B^|β| ≤ B^k`. Expanding the last power supplies the explicit
constant `C = (n!)^k` and exponent `N = n*k`. The theorem is independent
of number fields and applies to every positive matrix size.
