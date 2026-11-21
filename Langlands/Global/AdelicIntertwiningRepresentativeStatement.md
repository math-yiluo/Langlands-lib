# Representative independence for the adelic intertwining integral

`Langlands.Global.IntertwiningRepresentativeIndependenceStatement` is a
proposition, not a proof. It isolates the comparison needed to use the cocycle
relation with independently chosen Weyl representatives in the spectral family.

## Statement in the Library model

Let \(F\) be a number field in `Type`, \(G\) a connected reductive group over
\(F\), and \(P=MU\), \(Q=M'V\) parabolics with supplied rational Levi subgroups
and geometric unipotent radicals. The two multiplication maps are isomorphisms,
and the target Levi projection \(\pi'\) retracts \(l':M'\to Q\). Suppose
\((w_1,c_1)\) and \((w_2,c_2)\) are `IsWeylConjugation` data from \(P\) to
\(Q\), so that \(c_i:M'\to M\) is conjugation by \(w_i^{-1}\) in \(G\).
Instead of comparing cosets in a Weyl set, the statement tests equality of the
complex-linear maps
\[
 w_i : X^*(P)_F\otimes_{\mathbb Z}\mathbb C\longrightarrow
       X^*(Q)_F\otimes_{\mathbb Z}\mathbb C,
 \qquad \chi\longmapsto \chi\circ l\circ c_i\circ\pi'.
\]

For a common maximal compact \(K\) with both Iwasawa decompositions, and an
automorphic function \(\varphi\) on \(U(\mathbb A)M(F)\backslash G(\mathbb A)\)
in the supplied matrix and differential model, the conclusion is
\(M(w_1,\lambda)\varphi(g)=M(w_2,\lambda)\varphi(g)\) for every parameter and
adelic point. These are values of `IsIwasawaCompact.intertwiningOperator`, not
values of chosen meromorphic continuations. In this definition the Bochner
integral is zero where its integrand is not integrable. The statement does not
assert convergence. The density bridge uses the comparison only to transfer an
expansion identity on the sufficiently regular region.

## Provenance and proof obligation

In Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*
(JAMS 37, 2024), §2.1, p. 190 (PDF p. 4), \(W(P,Q)\) consists of the cosets
\(wM(F)\) with \(wMw^{-1}=M'\), and each such coset is uniquely determined by
its isomorphism \(\mathfrak a_P\to\mathfrak a_Q\). On the complexified dual
this is the parameter action. Section 2.2, p. 191 (PDF p. 5), defines the
intertwining integral with that coset as index. Mœglin–Waldspurger, *Spectral
Decomposition and Eisenstein Series* (1995), II.1.6, Proposition (i), pp. 87–88
(PDF pp. 10–11 of `06.1_pp_78_100_Definitions.pdf`), gives double-coset
independence in the convergence region; its preceding remark compares the
quotient by rational points with the adelic unipotent quotient.

The expected comparison in this model is algebraic before taking integrals.
Via restriction to the Levis, equality of the parameter maps means that the
normalizing point \(w_1^{-1}w_2\) acts trivially on \(X^*(M)_F\otimes\mathbb C\).
The rational characters restrict to a full-rank sublattice of the character
lattice of the split component \(A_M\), so this point centralizes \(A_M\).
Using \(Z_G(A_M)=M\) gives \(w_2=w_1m\) with \(m\in M(F)\). Since \(M\)
normalizes \(U\), the discrete subgroup defining the quotient of \(V(\mathbb A)\)
is unchanged, as is its measure induced by the same normalized Haar measure.
The source twist is left \(M(F)\)-invariant: this holds for \(\varphi\) by the
quotient condition and for the height factor by the rational product formula.
Consequently the integrands agree after identifying the quotients. The target
untwisting factors agree by equality of the parameter maps. This route would
also compare the total integral values without deciding integrability.

The sources work with standard parabolics; Bernstein–Lapid fix a maximal
compact in good position. This is a derived interface for independently
presented parabolics and any maximal compact satisfying the two specified
Iwasawa decompositions. Neither that comparison in the Library's data nor the
coset and integral argument just described is formalized in this module. It
adds an explicit premise to the density route, not an axiom or a theorem
establishing the spectral transform.
