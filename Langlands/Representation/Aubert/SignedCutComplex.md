# Signed differentials on cut diagrams

Author: Worker 164.

This internal algebraic prerequisite constructs a signed differential on a
commuting diagram of complex vector spaces indexed by finite cut sets. It also
constructs its homogeneous degree terms and proves that consecutive
differentials compose to zero. It does not assert exactness or effectivity.

For a linearly ordered type `ι`, `CutComplex.position s i` counts the elements
of `s` strictly less than `i`. The scalar `CutComplex.sign s i` is
`(-1 : ℂ) ^ position s i`. If an increasing exterior basis is assigned to `s`,
this is the insertion coefficient of left multiplication by the basis vector
for `i`: moving that vector past the smaller elements gives precisely this
number of sign changes. No exterior-algebra comparison for representation
theoretic graded pieces is asserted here.

`CutComplex.Diagram` consists of actual complex modules `Obj s`, linear maps
for cut inclusions, and their identity and composition laws. For its total
product `Total`, the elementary linear operator `step i` has target component

```text
(step i x)(s) = sign s i • map(s.erase i ⊆ s)(x(s.erase i))
```

when `i ∈ s`, and zero otherwise. Inserting the same cut twice gives zero.
For two distinct cuts, deleting the smaller cut decreases the position of
the larger cut by one; deleting the larger cut leaves the smaller position
unchanged. `sign_pair` proves that the resulting products of signs are
opposites. The diagram composition law identifies the two composite maps.
An explicit equality of their source cut sets handles the dependent module
types. Thus `step_pair` proves that the two orders cancel.

When `ι` is finite, `differential` is the sum of all the elementary operators.
The proof of `differential_square` pairs ordered pairs of cut insertions by
swapping the pair, using `Finset.sum_involution`. The diagonal terms are zero,
and every other pair cancels by `step_pair`.

`Degree k` is the product of the terms indexed by sets of cardinality `k`.
For finite `ι` this is a finite product, hence also the usual finite direct
sum of those modules. `extend k` extends a homogeneous family by zero and
`restrict k` restricts a total family. Restriction is a left inverse to
extension, so extension is injective. The total differential takes a family
supported in degree `k` to one supported in degree `k+1`: every nonzero
summand removes exactly one member of the target cut set. The map
`degreeDifferential k` is restriction of that differential after extension.
`extend_degreeDifferential` proves compatibility with the total differential,
and injectivity of extension then gives `degreeDifferential_square`.

The empty cut type is included: its only cut set is empty and all insertion
sums vanish. This module retains independent index and coefficient universes.
It constructs neither a smooth group action nor an Aubert-specific diagram;
those require a subsequent instantiation with the actual transition maps.

The provenance is internal: this is an elementary finite-diagram algebra
construction, with every sign and cancellation identity proved in Lean.
The generic diagram laws are hypotheses of the construction, not added
hypotheses of the signed-effectivity target. The actual Aubert application
must discharge them using the already constructed transition maps, and must
separately prove the required support, graded-map and exactness results.
