# Naturality of tensor dimension shifts

Proof author: Worker 45. Audit and documentation preparation: Worker 211.

A map of coefficient short exact sequences, together with a morphism in
the other tensor coefficient, induces a map of their tensor sequences.
The two commutative squares follow from functoriality of the actual
representation tensor product. Applying Mathlib's naturality theorem
for the Tate connecting morphism proves that each of the four tensor
shift isomorphisms is natural in both coefficients.

The proof uses the actual sequences and the proved short-exactness
certificates from `TensorShifts`; no commutation law is assumed.
This is an internal construction lemma for the dimension-shifting
approach to Serre, *Local Fields* (1979), Chapter VIII, section 3,
Proposition 5(i), printed p. 131 (PDF p. 137). It does not establish
the full cup-product naturality theorem by itself.

Source ID: `serre-1979-local-fields`; retained PDF SHA256:
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
