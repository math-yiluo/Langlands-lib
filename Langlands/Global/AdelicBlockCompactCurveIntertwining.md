# Compact curves and scalar section differentiation

An intertwiner for the actual infinite compact group takes values in the smooth compact-finite scalar sections. Suppose that a compact curve through the identity gives the derivative of a supplied source operator after applying every scalar linear functional. Then the intertwiner carries that source operator to the actual scalar section differential in the matrix tangent direction of the curve.

`smoothScalarSliceEvaluation` is the linear functional that evaluates a fixed finite slice at an infinite group point. The proof composes it with the intertwiner. Compact equivariance identifies its value on the translated vector with the scalar section evaluated on the corresponding right-translated curve. Both sides have derivatives at the identity. Uniqueness of the derivative and separation by all smooth finite slices give the result.

This is an internal application of the differential compatibility of a compact action in Getz and Hahn (2024), Definition 4.4.6, and of the normalized scalar section model in §10.1, pp. 270–271 (PDF 282–283).
