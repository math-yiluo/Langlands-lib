# Compatibility of local σ-lifts with character twists

`Langlands.BaseChange.sigmaLiftTwist` proves `SigmaLiftTwistStatement`
at its four independent universes. It gives the admissible distributional
form of Henniart–Lemaire, *Changement de base et induction automorphe pour
GL_n en caractéristique non nulle* (2011), II.2.9, Remark (4), printed
p. 70 (PDF p. 78), using the lift identity of II.2.7, printed p. 67
(PDF p. 75). The theorem uses the supplied twisted admissibility proofs
and intertwiner and preserves the original nonzero constant \(c\).

Write \(\chi_F(g)=\omega(\det g)\) and
\(\chi_E(g)=\omega(N_{E/F}(\det g))\). In a finite basis the algebra norm is
the determinant of the matrix of multiplication, a continuous function
for the module topology. This gives continuity of the induced map on units.
The embedding \(\mathbb C^\times\hookrightarrow\mathbb C\) supplies continuity
of \(\omega\) into the units. Van Dantzig's theorem supplies an open subgroup
basis for \(F^\times\), so the Library's continuous character theorem makes
\(\omega\) locally constant. Composing with the determinant and the norm
gives locally constant weights. Multiplying by these weights preserves the
local constancy and compact support of each Schwartz–Bruhat test.

The ordinary weight is constant on conjugacy classes because it takes values
in an abelian group. If \(\delta\) is associated with \(\gamma\), each
twisted conjugate \(x^{-1}\delta\sigma(x)\) is also associated with \(\gamma\).
`IsNormAssociated.norm_determinant_units_eq` then identifies its weight with
\(\chi_F(\gamma)\). `AreConcordant.mul_of_orbitValues` factors out that
common scalar on associated orbits and preserves vanishing on regular
non-norms. It gives concordance of the weighted tests for the supplied measures.

The integrated action of a twisted representation on a vector equals the
integrated action of the original representation against the weighted test.
At each group element, associativity of scalar multiplication moves the
character value into the test function. Equality of the action integrands
gives equality of the finite-rank integrated operators. Taking traces after
composition with the same linear map compares the twisted distributions.
For the base group the identity map gives the ordinary distributions.
Equality of the supplied intertwiners as functions gives equality as linear
maps. Applying the original lift identity to the weighted tests gives the
required distributional identity.

- Literature ID `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`
- SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`
