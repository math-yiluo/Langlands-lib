# Prescribed tensor realization for the isobaric automorphy proof

`CuspidalIsobaricTensorRealizationStatement` is the global realization input
in the place-by-place proof of Getz–Hahn (2024), Theorem 10.7.5, printed p. 288
(PDF p. 300). The finite data give irreducible admissible constituents in the
normalized induction for the supplied cuspidal block order. Their spherical
vectors outside the exceptional set define the restricted tensor of those
constituents. At each real and complex place, the input specifies the block
parameters of the actual cuspidal realizations and a quotient of the ordered
concatenation, with a subquotient map from the standard module in the original
block order. The conclusion asks for an equivariant surjection out of a
stable subspace of actual automorphic forms onto the tensor of the specified
modules for the common free operators. These conditions represent the use of
Langlands (1979), Lemma 1 and Proposition 2, printed pp. 203–206 (Corvallis I
PDF pp. 198–201), in Getz–Hahn, Theorem 10.7.1, p. 286 (PDF p. 298).

`cuspidalIsobaricAutomorphy_of_tensorRealization` proves the reduction to
this input. It takes the specified finite family, the proved complex-place
construction and the real-place construction from real generic standard
parameters and tied irreducibility. It applies the realization input to
these choices and descends their irreducible tensor to one quotient. It
restricts the finite tensor embedding to each finite place and composes the
archimedean embeddings with the quotient projections. This gives exactly
`Langlands.Global.CuspidalIsobaricAutomorphyStatement` from the stated inputs.
