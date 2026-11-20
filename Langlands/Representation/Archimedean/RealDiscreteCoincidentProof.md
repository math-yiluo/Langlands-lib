# Scalar commutant at coincident real discrete-series exponents

`Langlands.Archimedean.realTiedDiscreteCoincidentScalarCommutant` proves
`Langlands.Archimedean.RealTiedDiscreteCoincidentScalarCommutantStatement`.
The theorem concerns complex linear endomorphisms of the actual
`O(n)`-finite functions that commute with the compact group and the Lie algebra.

The proof first expands the weight-zero blocks and uses tied unlinked permutations
to put the list in the order used by `RealDiscreteNestedAssembly`. A nested
principal series surjects onto the tied standard module by adjacent tail maps and
unlinked swaps. A second principal series receives an injection by splitting each
discrete block into its high and low characters. The two series contain the same
signed character data.

`RealDiscreteDonorShift` constructs a weakly increasing shift of the donor, with
the parity of its signs, that gives a spherical series in the closed chamber.
Products of bottom-row minors with these weights give multiplication maps from
the spherical series to the donor. For any nonzero intertwiner from the donor
to the receiver, `RealBottomMinorJacquet` finds a nonzero coefficient at a
column family of smallest index sum. Upper triangular differentiation lowers
this sum in the correction terms. Their coefficients vanish there, so the
remaining coefficient is a Jacquet functional.

Spherical cyclicity gives nonvanishing on the spherical vector and trivial
Jacquet signs. The central character separates the multiset of normalized
Jacquet exponents. The resulting match of exponents and signs preserves a
signed residue after transporting receiver positions to donor positions.
`RealDiscreteMinorSelection` uses the rearrangement inequality on those
residues and the sum-of-squares bound for the column weights to identify the
column family with the permuted row family.

The spherical vector and this fixed family thus detect every nonzero
donor-to-receiver intertwiner by one linear functional. Composing any
endomorphism with the donor surjection and the receiver injection embeds the
commutant in that space of intertwiners. Subtracting a scalar multiple of the
identity to make its coefficient vanish proves scalarity. The argument uses
the actual tail maps, spherical cyclicity and the infinitesimal-character
calculation, so it also applies when exponents coincide.
