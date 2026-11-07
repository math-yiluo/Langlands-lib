# Compact left-translate integral summation

This internal prerequisite isolates the integral-summation part of a countable
Siegel covering argument. It applies to an arbitrary group and does not assert
cuspidal decay or an actual adelic covering theorem.

`leftTranslateCover a K` is the union of the sets `a i * K`. The index type is
arbitrary in the definition. The integral results require it to be countable.
For a left-invariant measure, `lintegral_leftTranslateCover_le` proves that a
nonnegative extended-real function bounded by `b i` on the translate `a i * K`
has integral on this union at most `(∑' i, b i) * measure K`. The translates
need not be disjoint. Neither the function nor `K` must be measurable for this
upper bound. The implemented proof uses subadditivity of the restricted lower
integral, comparison with a constant on each translate, left invariance of the
measure, and distribution of multiplication over an extended-real sum.

`lintegral_leftTranslateCover_lt_top` deduces finiteness when `measure K` and the
sum of bounds are finite. For a Hausdorff topological group with a compatible
Borel structure, `measurableSet_leftTranslateCover` proves that this union is
measurable when `K` is compact. It uses the compactness, hence closedness and
Borel measurability, of each continuous left translate, and countable union.

`lintegral_enorm_sq_leftTranslateCover_lt_top` applies the general bound to the
squared extended norm of any function into a seminormed additive group. Its
premises are a compact `K`, a measure invariant under left multiplication and
finite on compact sets, bounds `‖f (a i * x)‖₊ ≤ b i` for `x ∈ K`, and
`Summable (fun i => b i ^ 2)` for nonnegative real `b i`. Finiteness on compact
sets bounds the base measure. The pointwise norm bounds imply bounds for the
squared extended norms, and the nonnegative-real summability criterion makes
the corresponding extended-real sum finite. No regularity of `f` is required.

The provenance is internal: these are direct deductions from Mathlib's
countable-union lower-integral inequality, constant set-integral formula,
left-invariant measure identity, compact-set finiteness, and nonnegative-real
summability criterion. The remaining application must construct the actual
adelic covering and derive summable bounds from the original cuspidal
realization. This module does not prove the universal local-unitarity target.
