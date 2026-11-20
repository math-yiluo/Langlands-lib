# Compact pairing with a smaller standard vector

This is a derived step toward the spanning assertion in Jacquet's Proposition 7.1(v). Work in the upper Borel convention with the added character first. Let a compact-finite vector in the larger standard module have nonzero value at the identity. The proposition produces a compact-finite vector of the retained smaller standard module. The Haar probability integral of the larger vector at `diag(1,k)` times the smaller vector at `k⁻¹` has positive real part.

Lean constructs the block inclusion on matrices by separating the first coordinate and then maps units along it. It verifies the trailing row and determinant identities and the preservation of unitarity. Restricting the larger vector along this inclusion sends the span of its compact translates onto a space containing the compact translates of the restriction. On the diagonal circle torus the restriction at the identity has weight equal to the product of the retained characters. The normalized modulus factors are one there.

The compact coefficient separation theorem applies to this restriction and torus weight. The compact model extension theorem extends the resulting coefficient to the smaller standard module, preserving both its compact values and compact finiteness. This identifies its pairing with the positive pairing of the projected coefficient.

Source: Hervé Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §7.1, Proposition 7.1(v), pp. 44–46.
