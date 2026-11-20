# Ambient character parameters for Eisenstein series

In Bernstein–Lapid §6.1, the ambient real parameter of a standard parabolic
is obtained by restricting rational characters to the maximal split torus
in its Levi. The regularity condition in the Library uses restriction to
the Levi split component followed by an orthogonal lift. These descriptions
are compared in `EisensteinAmbientParameterLiftStatement` for a connected
reductive group with a compatible root presentation and a factorization
of the maximal split torus through the Levi. The statement equates the
two maps on every real parabolic parameter.

`EisensteinAmbientWeylParameterStatement` identifies the restricted real
part of the parameter transported by Levi conjugation in Bernstein–Lapid
§2.1. It uses a representative normalizing the common torus in the two
Levis, the actual conjugation morphism from the target Levi to the source
Levi, and a retraction of the target parabolic onto its Levi. The ambient
action is the relative Weyl class of that representative, acting on
characters by inverse precomposition.

`EisensteinAmbientParametersStatement` combines the two derived identities.
Together they express the actual parameters in the relative Weyl action
used in the chamber separation argument of Lemma 6.8 and §8.6.

[Bernstein–Lapid, On the meromorphic continuation of Eisenstein series](https://doi.org/10.1090/jams/1020)
