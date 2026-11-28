# Square-zero changes of affine coordinates and differential bases

Let \(A\) be a commutative \(R\)-algebra, let \(I^2=0\) in \(R\), and
let \(C\colon\Omega^1_{A/R}\to A\) be \(A\)-linear with image in \(IA\).
`addDerivation` is the algebra map \(a\mapsto a+C(da)\). The Leibniz rule
gives multiplicativity because the product of two values of \(C\)
vanishes. The derivation \(Cd\) vanishes on \(IA\) since it vanishes on
the \(R\)-scalars and has image in \(IA\). Consequently two such algebra
maps compose by adding their contractions. Negating the contraction
gives the inverse in `addDerivationEquiv`.

The homotopy contraction of this algebra map against the identity is
\(C\). The proof checks \(a\,db\), where the quadratic term in the two
contraction values vanishes, and extends by additivity. For a closed
one-form \(\omega\), the affine homotopy identity gives
\((1+Cd)^*(\omega)=\omega+d(C\omega)\).

For an \(A\)-module with basis \(b_k\) and a square-zero ideal \(J\subseteq A\),
`basisOfCongruentVectors` gives a basis with vectors \(w_k\) if every
\(w_k-b_k\) belongs to \(J\) times the module. The basis difference
extends to an endomorphism \(D\) with image in that ideal multiple.
Linearity gives \(D^2=0\), so \(1+D\) and \(1-D\) are inverse module maps.

The coordinate change implements the square-zero derivation description
of affine transitions in Kai-Wen Lan, *Arithmetic compactifications of
PEL-type Shimura varieties*, revised 14 March 2021, §2.1.3. The closed-form
formula uses the affine homotopy in Proposition 2.1.6.4. The basis
comparison is the corresponding elementary module calculation. The
retained source is `lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
