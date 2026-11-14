# Cofinal bounds over henselian separable extensions

This internal helper constructs the compatible cofinal valuative extension
needed to descend bounds over a henselian discretely valued field. It uses the
published normalized `henselianSeparableAddValuation` and the published descent
theorem `isAlgebraicallyBounded_of_geometricRationalPoint`.

Let `k` have a prescribed valuative relation and a compatible surjective
valuation `v : Valuation k (WithZero (Multiplicative ℤ))`. Assume its valuation
ring is henselian. For any separable field extension `K/k`,
`henselianSeparableCofinalValuativeExtension` supplies a valuative relation on
`K`, compatibility on embedded elements, and domination of every `K`-element
by the image of a nonzero `k`-element. The induced relation is exactly
`a ≤ᵥ b` if and only if the normalized additive value of `b` is at most that
of `a`.

Compatibility follows from the published normalization on nonzero base
elements, comparison of their integer logarithms, and separate zero cases.
For cofinality, the additive value of a nonzero extension element is a real
number `r`. Choose an integer `n ≤ r` and use surjectivity to select `b` with
`v(b) = exp(-n)`. Its normalized extension value is `n`, so its image
dominates the given element in the multiplicative valuative relation. The
zero element is dominated by `1`.

`isAlgebraicallyBounded_of_henselianSeparableExtension` applies the existing
cofinal descent theorem to actual scalar-extended rational points of an affine
scheme. Thus boundedness of their image, with respect to this constructed
extension relation, implies boundedness over the original prescribed relation.
Completeness, local compactness, finite extension degree, and assumptions on
the residue field are unnecessary. Bounds upstairs remain a premise.

The provenance is internal: these are consequences of the two published
interfaces named above and the Archimedean property of the real numbers,
rather than a new translation of an external source.
