# A single finite rank-one test for the prescribed L-factor

`PadicRankOneOrdinaryTestStatement` takes two actual admissible irreducible
`GL₁` representations, a unitary additive character, an additive Haar
measure, and a certificate that `P` is their JPSS L-polynomial. It produces
ordinary Whittaker functions of the prescribed opposite characters and a
Schwartz–Bruhat row test. With the canonical multiplicative and quotient
measures, the integral converges and equals `1 / P(q⁻ˢ)` throughout a right
half-plane. In particular the test admits the entire normalization one.

The proof `padicRankOneOrdinaryTest` uses `exists_tateCharacterModel` to
identify the two representations with quasicharacters. The two identity
functionals on the character lines give Whittaker functions whose product
is the product quasicharacter of the determinant. Representation
equivalence transports membership in the Whittaker sets. Uniqueness of
the certified polynomial identifies it with the abelian polynomial of the
product quasicharacter.

The test comes from `rationalLFactor_mem_scalarMellinRationalValues`. In
conductor zero this uses the integer-ring indicator and the geometric
series over valuation shells. In nonzero conductor it uses a normalized
compact open subgroup of integral units in the character kernel, so its
Mellin integral and the L-factor both equal one. The row test is the
pullback by the singleton coordinate equivalence. The rank-one quotient
measure identifies with the canonical Haar measure of `GL₁`, and the
scalar equivalence carries normalized multiplicative Haar measure to
that measure. These equalities transport both convergence and the value
of the scalar Mellin integral. The proof intersects its convergence
half-plane with those for rational evaluation and nonvanishing of the
polynomial denominator.

This is a derived statement for the Library's actual ordinary integrals.
The valuation-shell calculation follows Tate's *Fourier analysis in number
fields and Hecke's zeta-functions* (1967), §2.5, the p-adic computation on
printed pp. 319–322. The ramified unit test here uses the compact open
character kernel, and the Haar comparison and row-coordinate change are
implemented in Lean. The scalar results apply to the supplied `PadicField`
and its canonical data.
