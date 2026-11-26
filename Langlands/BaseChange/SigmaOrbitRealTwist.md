# Real determinant twists of σ-orbit products

The residue-normalized determinant norm is invariant under the entrywise Galois action. Consequently twisting a seed by a fixed real determinant power preserves the equivalence tests with its conjugates. Use the inverse twist on an equivalence of twisted actions to recover an equivalence of the original actions.

`sigmaOrbitProduct_realPowerTwistEquiv` moves the common twist across normalized induction on the actual orbit product. It uses the determinant-twist isomorphism for smooth induced sections and the block equivalences from Galois invariance. `exists_unitary_realPowerTwist` applies the real unitarization theorem for an irreducible supercuspidal to the same-carrier p-adic model of `E`. The resulting twist is irreducible and supercuspidal by the determinant-twist lemmas. These are the local operations used to reduce the essentially σ-discrete orbit of Henniart–Lemaire II.4.12 to the σ-discrete orbit in II.4.6.
