# Actual Cartan–Iwasawa weight comparison from standard-basis data

`Langlands.HarishChandraSchwartz.RationalCartanIwasawaWeightComparisonOfBasisStatement`
is a proposition at arbitrary universe `u`. It uses an affine, locally
finite-type group scheme over a nonarchimedean local field \(F\), a maximal
split torus \(i:S\to G\), and the standard groups indexed by a cocharacter
\(\nu\) of \(S\). All subgroups and weights in the inequalities are on actual
rational points with their rational-point topology.

The proposition assumes a compact open subgroup \(K_0\) with
`SimultaneousStandardBasisAt i ν K0` and a finite family \(F_0\) in
\(Z_G(S)(F)\). It also takes a compact open subgroup \(K\) with a supplied
Iwasawa factorization \(G(F)=P_0(F)K\) for the empty-index standard parabolic
\(P_0\). Write \(\delta_0\) for the actual Haar modulus of conjugation on the
empty-index standard unipotent subgroup, and
\(\phi_K(pk)=\delta_0(p)^{1/2}\).
There is a real constant \(C>0\) such that for every cocharacter \(y\)
with nonnegative pairing with each simple relative root, and every
\(g\in \bigcup_{f\in F_0}K_0\,i(y(\varpi))\, f K_0\), one has
\[
\phi_K(i(y(\varpi)))\le C\phi_K(g).
\]
The constant is uniform in both \(y\) and \(g\).

This is a derived lattice-cell form of Waldspurger's modulus comparison
in Lemma II.3.2, used in the proof of Lemma II.4.4. The simple-root
conditions give \(\lvert\alpha(i(y(\varpi)))\rvert_F\le 1\), the weak
chamber convention of I.1. The standard-basis hypothesis makes the
published double-coset volume estimate from I.1 (5) available at \(K_0\).
The factorization subgroup \(K\) and the finite centralizer factors are
those of the global Xi estimate's actual-point setting.

Source. J.-L. Waldspurger, *La formule de Plancherel pour les groupes
\(p\)-adiques (d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003),
I.1 (5), p. 241, Lemma II.3.2, p. 255, and the proof of Lemma II.4.4,
p. 262. Registered source `waldspurger-2003-plancherel`,
SHA-256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
