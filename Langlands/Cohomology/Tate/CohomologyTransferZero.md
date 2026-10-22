# Ordinary transfer on invariant zero-cocycles

Authors: Worker 45 and Worker 210. Worker 45 wrote the Lean proof; Worker 210
audited it and prepared the accompanying documentation.

The coordinate lemmas evaluate Mathlib's bar-to-standard comparison on basis
vectors. The forward map acts by the first homogeneous coordinate on the
inhomogeneous cochain evaluated at successive ratios; the inverse evaluates at
the partial-product tuple. These formulas follow from the existing explicit
bar/standard basis formulas and the free representation's universal property.

For an invariant zero-cocycle, each subgroup action in the ordinary relative
trace fixes the coefficient. Its value is therefore exactly the sum over left
cosets defining `cosetNorm`. This is an internal comparison proof for the
independent ordinary transfer, using Serre, *Local Fields* (1979), VII section 7,
printed pages 118–119, and VIII section 2, printed pages 129–130.
Source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The common carrier universe remains arbitrary.

Passing to the explicit degree-zero short-complex homology data sends this
coset norm to its class modulo the full norm image. Thus the comparison from
the restricted zero splice to the actual Tate complex has the expected
coset-norm formula on every invariant representative. The proof uses the
kernel and cokernel compatibility equations of the induced homology map.
