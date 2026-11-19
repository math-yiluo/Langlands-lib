# Casselman depth for bi-invariant coefficient tensors

Worker 253's `coefficientTensorBiAverage` averages the vector and smooth
functional at one compact open level. The accompanying
`coefficientTensorMap_biAverage_eq` preserves the original bi-invariant
coefficient.

`IsStandardCasselmanDepthBound.coefficientTensorMap_eq_mul_constantTerm` then
applies the rank-dependent Casselman identity to dominant uniformizer points.
The averaged vectors and smooth functionals are fixed at the chosen basis
level. Each pure tensor therefore satisfies the same identity once the depth
outside the parabolic face bounds the fixed-vector dimension times the
geometric constant. The comparison with the chosen standard constant term
uses the explicit coefficient of one actual stable pairing and the radical
half-modulus formula. Tensor linearity gives the equality for every
bi-invariant coefficient tensor. The number of pure tensors does not enter the
depth bound.

This is a derived application of Waldspurger's Proposition I.4.3 (printed
p. 245) and Proposition I.6.2 (printed pp. 249–250) in *La formule de
Plancherel pour les groupes p-adiques (d'après Harish-Chandra)*. It supplies
the fixed-level coefficient identity needed for the uniform threshold in
Lemma VI.2.3.
