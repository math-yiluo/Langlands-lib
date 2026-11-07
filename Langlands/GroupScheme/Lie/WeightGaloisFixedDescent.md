# Effective Galois descent of actual adjoint weight spaces

This internal deduction restricts actual Lie-vector Galois descent to character
weight spaces. The ambient group is affine and locally of finite type over an
arbitrary field, and the original acting torus is split. Every character is
included, including zero. The Galois extension need not have finite degree.

`schemeScalarExtension_mem_extendedWeightSpace_iff` reflects membership of an
original vector in the scalar-extended span of its weight space. Apply scalar
extension to the quotient map by the original weight space: it kills all
generators of the extended span. If the extended original vector lies there,
the pure tensor of its quotient class vanishes. Faithful flatness of a field
extension forces the original quotient class to vanish. The forward
inclusion follows from the definition of the extended span. This step works
for arbitrary acting tori and arbitrary field extensions.

For a split acting torus, the published equality between the base-changed
weight space and the scalar-extended original span gives
`schemeScalarExtension_mem_weightSpace_iff`.

`baseChangeFixedWeightSpace` is the additive subgroup of the actual
base-changed character weight space fixed by every canonical ambient
semilinear Galois map. Its definition needs neither splitness, local finite
type, nor a Galois extension. `weightSpaceGaloisFixedEquiv` is the additive
equivalence from the original weight space to that fixed subgroup. Its forward
map is the previously constructed actual Lie-vector extension. Surjectivity
uses effective Lie descent, and membership reflection puts the descended
vector back in the original weight space.

The provenance is internal, through actual Lie scalar extension, the quotient
map of a submodule, faithful flatness, the published split-torus weight-space
base-change equality, and actual Lie-vector Galois descent. This module does
not identify a relative weight space with a root-orbit tuple or prove
restriction-fiber transitivity, field coordinates on root points, or apartment
existence.
