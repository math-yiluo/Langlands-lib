# The self-pair denominator of a normalized product of discrete series

`normalizedProductSelfPairPolynomials` takes a positive-rank standard block
shape over a bundled p-adic field and irreducible square-integrable block
actions. It gives the certified denominator `D i j` of each block paired
with the smooth contragredient of block `j`, together with a certificate
that their double product is the denominator of the normalized induced
representation paired with its actual smooth contragredient.

The proof uses admissible smooth duality to preserve irreducibility and
square integrability of the dual blocks. The Library's `temperedLFactor`
gives the multiplicative formula for induction of the two block families.
`normalizedProductSmoothDualEquiv` then identifies the second induced
action with the smooth dual of the original induction. Equivalence of
representations transports the polynomial certificate. The product
formula applies in particular to the upper orbit in the σ-lift structure
argument of Henniart–Lemaire.

Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
caractéristique non nulle*, Mém. SMF 124 (2011), II.3.5(iii), printed p. 80
(PDF p. 88), and its self-pair use in II.4.12, printed p. 96 (PDF p. 104).
Literature ID `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`,
SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
