# Exponent expansions of Bruhat piece integrals

`StandardParabolicFamily.PieceIntegralExponentExpansionStatement` concerns a
`StandardBruhatPiece` for standard parabolics \(P_I,P_J\) over a number
field \(F\). Its
source is \(P_{I_1}\subseteq P_I\), and its target is \(P_{J_1}\subseteq P_J\).
Fix a compact subgroup \(K\) of \(G(\mathbb A_F)\) with
\(P_{I_1}(\mathbb A_F)K=G(\mathbb A_F)\) via the composite source
inclusion \(P_{I_1}\to P_I\to G\). The resulting Iwasawa height supplies the
twist by \(\lambda'\) in the integrability hypothesis and in the whole and
component integrals below.

The piece identifies the two smaller Levis by Weyl conjugation. Write \(W\) for
the corresponding parameter pullback using the specified retraction onto the
target Levi, \(\lambda'\) for \(\lambda|_{P_{I_1}}\), and \(\rho_H\) for the
half-modulus parameter of \(P_H\).

Suppose \(C_{I_1}\phi\) has a finite expansion indexed by distinct raw parameters
\(\nu\). The constant term and every component are continuous and left
\(U_{I_1}(\mathbb A)\)-invariant. Each component has a polynomial orbit of degree
at most \(k\) along the positive split component of \(P_{I_1}\). At a parameter
where the piece integrand is integrable at every base point, the piece integral
is the sum of the intertwining integrals of those components. Each integral has
a polynomial orbit of degree at most \(k\) along the positive split component of
\(P_{J_1}\), with raw label

\[
  W(\nu-\rho_{I_1}+\lambda')+\rho_{J_1}.
\]

Each integral belongs to the span of positive split translates along \(J_1\) of
the whole piece integral. This statement concerns the integral at the smaller
target \(P_{J_1}\), before the sum over \(P_{J_1}(F)\backslash P_J(F)\).

`StandardParabolicFamily.pieceIntegral_exponentExpansion` uses
`subgroupConstantTerm_congr_hom` and `intertwining_congr_hom` to pass from the
composite inclusions of the piece to the standard parabolic and unipotent
inclusions. The same comparison transports integrability. The proof applies
`intertwiningIntegral_exponentExpansion` to the given components. The transported
Haar factor from `hasPolynomialOrbit_intertwiningIntegral_halfModulusOffset`
gives the offset \(\rho_{J_1}-W(\rho_{I_1})\). Linearity of \(W\) rewrites the label
in the form above. The morphism congruences then identify each integral and
their sum with the expressions for the original piece.

This is the integral step in the exponent inclusion of Lapid, *On Arthur's
asymptotic inner product formula of truncated Eisenstein series* (2011),
Proposition 4 and (13), pp. 321–322. Bernstein–Lapid, *On the meromorphic
continuation of Eisenstein series* (2024), (6.4)–(6.5), p. 201, give the
intertwining covariance and its Haar character. Their formula (6.17), p. 208,
places these integrals inside the sum over rational cosets.
