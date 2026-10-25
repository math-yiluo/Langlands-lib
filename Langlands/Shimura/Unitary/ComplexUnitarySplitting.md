# Actual complex unitary group splitting

This internal construction restricts the published Harris similitude splitting
to its actual multiplier kernel. It retains the central-simple datum and Harris
signature charts. The input contains no output group-scheme isomorphism.

The scalar-algebra equivalence `iteratedScalarUnitarySplitting` identifies the
unitary elements with one invertible matrix at each real embedding of the
totally real field. It uses `unitaryEquivKernel` and the proved fact that the
second component of `iteratedScalarGroupSplitting` is the multiplier. Its inverse
sets this component to one. The matrix formula and inclusion formula show that
these are the existing coordinates, with precisely multiplier one.

`complexRationalUnitaryGroupScheme` is the existing rational unitary group
pulled back from Q to R to C. The real scalar-extension comparison gives its
points as unitary elements in the iterated scalar algebra, on every complex
test scheme. Restriction maps are the original tensor coefficient maps.
Composing with the scalar-algebra equivalence gives `complexUnitaryPointsEquiv`;
its naturality is entrywise matrix restriction, proved from naturality of the
existing matrix splitting.

The finite product is the categorical product of the published GL group
schemes indexed by the real embeddings. Its natural point equivalence yields
the actual group-scheme isomorphism `complexUnitaryGroupSchemeIso` by the
published group-valued Yoneda construction. This establishes a scheme
isomorphism, rather than only a bijection of complex-valued points. It is
conditional on the supplied signature charts and makes no new assertion of
chart existence, reductivity, smoothness, or Shimura moduli representability.

The result is derived internally from the published scalar, unitary-kernel,
and similitude-splitting constructions. The proof restricts an existing
product equivalence to its multiplier kernel, checks naturality on all test
schemes, and applies the existing reconstruction of scheme isomorphisms from
natural point equivalences. The forward and inverse scheme-isomorphism point
formulas verify that the resulting morphisms realize exactly the selected
matrices at every real place. All new code is by Worker 57.
