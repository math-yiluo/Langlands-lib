# Tensor exactness and coefficient shifts

Proof author: Worker 45. Audit and documentation preparation: Worker 211.

This internal development supports the tensor-exactness hypotheses in Serre,
*Local Fields* (1979), VIII §3, Proposition 5, printed pages 131–132.
Source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

The module proves that a retract of a short exact sequence of modules is short
exact by explicitly lifting kernels and targets. Consequently, tensor exactness
passes to a scalar retract of a coefficient module. Finite-product coordinates
identify a tensor with the underlying coinduced module with a finite product of
the original tensors. Exactness is then proved coordinate by coordinate. The actual positive and negative coefficient shifts are scalar retracts of the coinduced module, using the proved splittings of their cokernel and kernel sequences. Therefore tensor exactness for a coefficient implies tensor exactness for either shift.

These are internal linear-algebra certificates, not assumed flatness conditions
or hypotheses supplying cup-product compatibility. They use the actual
coinduced module from `Coinduced`, the coefficient sequences from
`ShiftDefinitions`, and Mathlib's tensor products and short complexes.
The tensor braiding transports the same results to tensoring on the other side.
All carriers retain universe `u`.
