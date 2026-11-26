# Determinants of matrix norms over cyclic algebras

`IsCyclicAlgebra.prod_powers_eq_algebraMap_norm` identifies the determinant
norm of an element \(x\) with \(\prod_{i=0}^{l-1}\sigma^i(x)\) after embedding
the base field in the cyclic algebra. Applying \(\sigma\) rotates the factors
because \(\sigma^l=1\), so the product comes from the base field. The
coordinates supplied by `CyclicAlgebraStructure.exists_coordinates` express
the algebra as \(r\) copies of one cyclic field extension of degree \(d\).
Project to that field and write each exponent as \(rj+i\), where
\(0\le i<r\) and \(0\le j<d\). The wrap automorphism acts \(j\) times on
coordinate \(i\). Interchanging the two finite products gives the field norm
of each coordinate by `IsCyclicAlgebra.norm_eq_prod_powers`.
`Langlands.Global.AdelicFunctoriality.norm_pi` identifies their product with
the algebra norm. The scalar embedding into the residue field is injective,
so the computation there determines the scalar.

`IsCyclicAlgebra.determinant_cyclicNorm_eq_algebraMap_norm` applies determinant
multiplicativity and naturality to the ordered matrix norm, then uses the
scalar formula. `IsNormAssociated.norm_determinant_units_eq` applies the
determinant to the defining conjugacy. The determinants of the conjugating
matrix and its inverse cancel. Naturality for the scalar embedding and
injectivity yield \(N_{E/F}(\det\delta)=\det\gamma\) as an equality
of units. The argument works in every matrix rank and for split and
partially split cyclic algebras.

These algebraic identities follow from the cyclic product and norm conventions
of Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n
en caractéristique non nulle* (2011), I.2.1, printed pp. 10–11 (PDF pp. 18–19).
The determinant comparison gives the matching of weights in II.2.9,
Remark (4), printed p. 70 (PDF p. 78).

- Literature ID `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`
- SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`
