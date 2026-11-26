# Nonvanishing of a norm-twisted supercuspidal pair denominator

For an irreducible square-integrable supercuspidal `π` over a bundled p-adic
field `F` and a character `κ` trivial on the norms of a finite extension,
`normTwistedSupercuspidalSelfPairPolynomial` gives the certified
Rankin–Selberg denominator of `(π, κπ∨)` and its nonvanishing at `q_F`.
The polynomial is unique by `IsPadicRankLPolynomial.unique`.

The field norm of a scalar is its extension-degree power. Hence each value
of a norm-trivial character has finite order and modulus one. Smooth duality
preserves square integrability and supercuspidality, and the unit-modulus twist
preserves unitarizability. The equal-rank supercuspidal formula writes the
denominator as a product of `1 - a X` with `‖a‖ = 1`, so its evaluation at the
real residue cardinality greater than one cannot vanish.

This supplies the `s = −1` nonvanishing of the lower factors in the proof of
Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
caractéristique non nulle*, Mém. SMF 124 (2011), II.4.12, printed p. 96, from
the same-field formula II.3.5(i), printed p. 80. Literature ID
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`,
SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
