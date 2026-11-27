# Compact local coefficients for supercuspidal globalization

For a finite completion of a number field, `globalizationLocalCoefficient` sends a
vector `z` to the cutoff inverse coefficient `g ↦ ℓ(ρ(g⁻¹)z)`. The cutoff is supported on
the determinant-unit subgroup. It comes from the compact determinant-unit coefficient,
extension by zero, and pullback by inversion. The completion's valuation and the residue-normalized
absolute value give the same determinant-unit condition. Smooth dual separation supplies a
vector and a covector with pairing one for each irreducible supercuspidal representation.

Left translation by a determinant-unit matrix acts through its action on `z`. For a translated
radical integral, this identity and left invariance of Haar make the integral, as a linear
functional in `z`, invariant under the conjugated radical. Its Jacquet quotient is zero by
supercuspidality, so the integral vanishes. Compact support and the closed radical embedding
ensure absolute integrability. This is the local matrix coefficient input to the cuspidal-test
method in Getz–Hahn, *An Introduction to Automorphic Representations* (2024), Definition 16.4.1
and Lemma 16.4.2, printed p. 430.
