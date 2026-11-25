# Upper triangular Lie derivatives of the archimedean block evaluation

`placeCoefficientLieSum` sums the local Lie operators of the actual inducing blocks on their respective slots of one place's coefficient tensor. The operators act on the cuspidal coefficient spaces in the chosen all-place spectral decompositions.

The real and complex upper triangular derivative formulas evaluate a standard vector at the compact identity after applying its Lie action. The result is the derivative of the normalized half modulus times the original evaluation, plus the sum of actual block operators in the diagonal block directions. The proof uses the affine parabolic curve with the given tangent. Its one-place adelic inclusion gives the same normalization derivative as the adelic scalar section formula. The tensor of the local standard-to-coefficient equivalences transports each block Lie operator to the corresponding actual cusp coefficient operator.

This comparison is internal to the inducing model for `CuspidalIsobaricAutomorphyStatement`. Getz and Hahn (2024), §4.4, Definition 4.4.6, give the Lie differentiation setting. Their §10.1, pp. 270–271 (PDF 282–283), gives the normalized scalar model. The Lean proof uses the Library's standard right derivatives, one-place normalization identities, and actual cuspidal coefficient equivalences.
