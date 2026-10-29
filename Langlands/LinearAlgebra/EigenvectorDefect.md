# Powers of an eigenvector defect

The theorem `Langlands.ScalarLayer.pow_sub_smul_apply_of_eigen` states that,
for a complex vector space `X`, an endomorphism `L`, and an eigenvector equation
`L x = μ • x`, every complex scalar `c` and natural number `k` satisfy

`((L - c • 1) ^ k) x = (μ - c) ^ k • x`.

The proof is induction on `k`, using linearity to evaluate the successor power.
There is no nonzero-vector or finite-dimensional hypothesis.

The Integrator moved this existing declaration, with its statement and proof
unchanged, from
[TemperedOppositeJacquetScalarLayerAssembly](../Representation/Classification/TemperedOppositeJacquetScalarLayerAssembly.md).
Its namespace and public name are retained, and the original module imports it.
[AdmissibleCentralDualToPrimalProof](../Representation/Exponents/AdmissibleCentralDualToPrimalProof.md)
uses the same declaration in place of its identical private copy. The shared
module imports only Mathlib, keeping this algebraic identity available without
the classification assembly.
