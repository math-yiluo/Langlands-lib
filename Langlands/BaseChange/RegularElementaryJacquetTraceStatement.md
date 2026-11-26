# The regular elementary Jacquet trace formula

`Langlands.BaseChange.RegularElementaryJacquetTraceStatement` states the
strict-weight case of Henniart–Lemaire I.5.3 for \(\mathrm{GL}_{r+1}(E)\).
Here \(E\) is a canonical p-adic field with residue cardinality \(q_E\),
\(\tau\) is a \(\mathbb Q_p\)-algebra automorphism, and \(\varpi\) has
additive order one and is fixed by \(\tau\). The strictly decreasing
integer weight \(\nu\) specifies
\[
t=\operatorname{diag}(\varpi^{\nu_i}),\qquad
\rho(\nu)=\sum_{i<j}(\nu_i-\nu_j).
\]
Write \(B=TN\) for the upper triangular Borel with diagonal torus \(T\).
For an irreducible admissible complex representation \(\Pi\) and a
`SigmaIntertwiner` \(A\) satisfying \(A\Pi(g)=\Pi(\tau(g))A\), the equality is
\[
\operatorname{tr}_{\mathrm{fr}}\!\bigl(\Pi(\phi_\nu^\tau) A\bigr)
  = q_E^{\rho(\nu)}
    \operatorname{tr}_{(\Pi_N)^{T(\mathcal O_E)}}\!
    \bigl(\Pi_N(t) A_N\bigr).
\]
The equality is stated for every positive rank, with independent universes
for \(E\) and the vector space of \(\Pi\).

## The operators and the fixed space

The function \(\phi_\nu^\tau\) is `regularElementaryTest`, the indicator of
\(\{k^{-1}tm\,\tau(k) : k\in K_E,\ m\in T(\mathcal O_E)\}\).
`sphericalHaar` gives \(K_E=\mathrm{GL}_{r+1}(\mathcal O_E)\) mass one.
`twistedDistribution` takes the finite-rank trace of the integrated action
composed with \(A\).

`Parabolic.leviCoinvariants` for the singleton-block shape is the
unnormalized action \(\Pi_N\) on the upper unipotent coinvariant quotient.
`jacquetSigmaIntertwiner` sends \([v]\) to \([Av]\) on that quotient.
`integralDiagonalLevi` is the preimage of \(K_E\) under the continuous
embedding of the product Levi. The proof of `mem_integralDiagonalLevi_iff`
identifies each singleton-block Levi element with its ambient diagonal
matrix and uses the integral matrix and inverse conditions, which say
that each coordinate is an integral unit. `mem_borelJacquetFixed_iff`
then identifies the fixed submodule with the vectors fixed by every
integral diagonal. Its finite dimensionality follows from
`Parabolic.isAdmissible_leviCoinvariants`.

The diagonal action preserves the fixed subspace by commutativity of the
torus. The descended intertwiner preserves it because the field
automorphism and its inverse preserve the order of every coordinate.
`borelJacquetDiagonalAction` and `borelJacquetFixedTwist` restrict these maps
to that subspace. Their composition is the endomorphism used in
`LinearMap.trace`.

## Source correspondence

The regular case of I.4.1–I.4.2 gives the indicator used here. The
partition of a strict weight has singleton blocks. Thus the Levi in
I.5.2–I.5.3 is \(T(E)\), whose blockwise twisted-regular set is all of
\(T(E)\). The Levi measure in I.4.2 gives \(T(\mathcal O_E)\) mass one.
Integrating over the translate \(tT(\mathcal O_E)\) amounts to applying
\(\Pi_N(t)\) after the averaging projection onto
\((\Pi_N)^{T(\mathcal O_E)}\). The probability Haar measure on the compact
subgroup is preserved by the twist, so the projection commutes with \(A_N\).
This accounts for the fixed-space trace in the statement.

In I.5.3 the cyclic unramified extension \(E/F\) has degree \(\ell\).
The base uniformizer maps to the uniformizer used upstairs and is fixed by
the generator. This is the choice made by `regularElementaryBaseChangeTests`.
The source factor \(q_F^{\rho(\ell\nu)}\) is \(q_E^{\rho(\nu)}\), since
\(q_E=q_F^\ell\) and \(\rho(\ell\nu)=\ell\rho(\nu)\). The Borel modulus at
\(t\) is \(q_E^{-\rho(\nu)}\), from the product of \(\lvert t_i/t_j\rvert_E\)
for \(i<j\). The inverse square root of the modulus in the normalized
Jacquet action therefore changes the outside factor to
\(q_E^{\rho(\nu)/2}\), as in the normalization used in I.5.4, Lemma 2.

For a cyclic twist of order \(\ell\), \(A^\ell\) is an invertible scalar.
It commutes with the representation and has an eigenvector in a nonzero
finite-dimensional space of open-subgroup fixed vectors. Irreducibility
then makes its eigenspace the whole representation. This gives the
strongly irreducible pair of I.5.1, with \(A\) left at its supplied scalar.
`regularElementaryJacquetTrace_of_identity` derives the ordinary formula
from the twisted statement by taking the identity on the representation
and on the quotient. It applies to the ordinary member of the base-change
pair at weight \(\ell\nu\).

The module states the trace identity. The Weyl exponent expansion for
principal series in I.5.4–I.5.5 is a separate result.

Guy Henniart and Bertrand Lemaire, *Changement de base et induction
automorphe pour \(\mathrm{GL}_n\) en caractéristique non nulle*, Mém. SMF
124 (2011). I.4.1–I.4.2, printed pp. 26–28 (PDF pp. 34–36), specify the
test and Levi measure. I.5.1–I.5.2, printed pp. 28–30 (PDF pp. 36–38),
give the twisted distribution and quotient conventions. I.5.3,
Proposition, printed pp. 31–32 (PDF pp. 39–40), gives the unnormalized
identity. I.5.4, Lemma 2, printed p. 35 (PDF p. 43), gives the half-power
normalization. [Original publication](https://www.numdam.org/item/MSMF_2011_2_124__1_0/).

Registered literature ID
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`.
SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
