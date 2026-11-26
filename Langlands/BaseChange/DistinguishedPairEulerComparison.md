# Comparing distinguished Euler denominators in completed pair equations

`DistinguishedPairEulerFromEquationsStatement.{u,v}` compares two forward polynomials
\(P,Q\) with constant coefficient one. It takes two `HasGlobalEquation` packages,
with finite place types in independent universes and archimedean factors given by
lists of Gamma blocks. The four polynomials \(P,P_d,Q,Q_d\) are expressed in one
variable \(x=q^{-z}\) with \(q>1\). On some right half-plane, multiplying the
respective finite product limits by the indicated polynomials gives a common forward
product and a common dual product. The total epsilon multipliers are analytic and
nonzero at every point. For each pair of forward and dual polynomials, a nonzero
forward root \(x\) must avoid the roots of its dual at \(q^{-1}/x\).

`distinguishedPairEulerFromEquations` proves \(P=Q\) under these hypotheses. Uniqueness
of the product limits and meromorphic continuation give \(P L=Q U\) and
\(P_d L_d=Q_d U_d\) in the spectral variable, where \(L,U\) are the two finite forward
products and \(L_d,U_d\) the finite dual products. The proof clears the archimedean
denominators in the two functional equations and cancels the common upper dual
meromorphic germ. The resulting germ identity has \(P\) times the reflected \(Q_d\)
on one side and \(Q\) times the reflected \(P_d\) on the other, each multiplied by
the corresponding epsilon multiplier and two archimedean reciprocal denominators.

For each \(x\ne0\), choose \(z\) with \(q^{-z}=x\) by taking a logarithm and adding
integral multiples of the imaginary period. Its imaginary part can exceed the finitely
many absolute imaginary parts of all Gamma shifts. At this point the four archimedean
reciprocal denominators are nonzero, including those evaluated at \(1-z\).
At a root of \(P\), the multiplier of \(Q\) is analytic and nonvanishing by the
separation hypothesis for \(P_d\). The multiplier of \(P\) is analytic, so its
order is nonnegative. Equality of the germs bounds the multiplicity in \(P\) by
the multiplicity in \(Q\), using `meromorphicOrderAt_eval_spectralPoint`.
At a root of \(Q\) the other separation hypothesis gives the reverse inequality.
Neither polynomial vanishes at zero. Their root multisets then agree, and the
common constant coefficient fixes the leading coefficient in the split
factorizations over \(\mathbb C\).

The comparison is the analytic step of the global-to-local argument in
Henniart–Lemaire, *Changement de base et induction automorphe pour GLₙ en
caractéristique non nulle* (2011), II.6.19, equations (3)–(5), printed pp. 133–134
(PDF pp. 141–142). The retained source ID is
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`
and its SHA-256 is `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
The analogous Euler comparison principle is Arthur–Clozel, *Simple Algebras, Base
Change, and the Advanced Theory of the Trace Formula* (1989), Chapter 1, §6.4,
Lemma 6.11, printed pp. 65–66 (PDF pp. 79–80), source ID
`arthur-clozel-1989-base-change`, SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
Here the product equality after clearing the four denominators is a hypothesis.
The logarithmic period argument in `DistinguishedEulerPolynomialVanishing` is
adapted to compare the full orders of the two forward factors.
