# Actual segment products in an ordered refinement

Author: Worker 494.

This internal construction retains the supplied actual smooth representation
at every segment occurrence of an ordered refinement. It is derived from
the published block-list construction, shape extensionality, and the closed
ordered normalized-product regrouping theorem.

The block-list round trip and injectivity lemmas show that equality of the
complete dependent block lists identifies the full product data.
`inducedEquivOfBlockListEq` gives an actual representation equivalence in
that situation. Equality of segment lists alone is insufficient.

`inducedEquivOfShape` expresses a datum's actual normalized product on an
equal ordered shape, retaining all rank transports of its supplied factors.
`refinementDatum` constructs the actual data in one specified inner shape.
Its block list is the original supplied occurrences selected by the label
bijection. Its degree sum follows from the supplied size identities, and its
shape is exactly the corresponding inner refinement.

`refinementDatumProductEquiv` identifies the geometric inner normalized
product with the actual product of that inner datum. `refinementInducedEquiv`
uses the independently proved ordered regrouping theorem and these
identifications to compare the original flat product with the outer product
of actual inner data. The label bijection, size law, and exact ambient
coordinate law remain explicit.

Field and segment universes are independent; actual block carriers use their
maximum, as in `SegmentProductDatum`. No segment-socle existence, commutation,
linked reduction, ordered strong socle, or exhaustion statement is proved.
