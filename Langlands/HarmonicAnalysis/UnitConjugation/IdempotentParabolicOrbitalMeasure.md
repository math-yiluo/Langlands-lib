# The ambient orbital measure in parabolic coordinates

`orbitalPoint` sends a left coset \(H g\) of the unit stabilizer of \(X\) to
\(g^{-1}Xg\). It is continuous for the quotient topology, and composition
with a test function gives `orbitalIntegrand`.

For an idempotent \(e\) in a finite-dimensional normed algebra \(A\) over
a proper nontrivially normed field, write \(M\) for the centralizer algebra
and \(N=eA(1-e)\). Let \(X\in M\) be regular in \(A\), and suppose
\(A^\times=PK\) with \(P\) the upper triangular unit subgroup and \(K\)
a compact open subgroup. Let \(J\) and \(H\) be the stabilizers of \(X\)
in \(M^\times\) and \(A^\times\). Use compatible quotient measures
\(\nu_M,\nu_G\) on \(J\backslash M^\times,H\backslash A^\times\), with
matching two-sided Haar measures on \(J,H\) under the inclusion. Use
the restriction \(\mu_K\) of ambient Haar on \(K\).

`parabolicOrbitalPoint` is the continuous map
\[
 (Jm,Z,k)\longmapsto k^{-1}(m^{-1}Xm+Z)k.
\]
The theorem `map_parabolicOrbitalPoint` gives an additive Haar measure
\(\nu\) on \(N\) and a positive finite scalar \(c\) such that the pushforward
of \(\nu_M\times\nu\times\mu_K\) by this map is \(c\) times the pushforward
of \(\nu_G\) by the ambient orbit map.

First, the group Haar factorization gives the pushforward of the Levi,
upper and compact measures along \((m,Z,k)\mapsto m(1+Z)k\), with scalar
\(c\). The compatible-quotient product formula passes this through the
common stabilizer. At a representative \(m\), put \(Y=m^{-1}Xm\).
Conjugation by \((1+Z)^{-1}\) sends \(Y\) to \(Y+[Y,Z]\). The upper-corner
change of variables sends the initial upper Haar to a single measure
\(\nu\) for every such \(Y\). Tonelli's theorem applies that change on
each Levi coset. Testing against indicators gives the pushforward identity.

In Harish-Chandra's *Admissible invariant distributions on reductive
\(p\)-adic groups*, §1.2, printed pp. 7–8, the computation around
Lemmas 1.5 and 1.6 uses normalized orbital integrals over right
quotients by the split Cartan component. The measure formula here
applies the same change of variables to left quotients by the full unit
stabilizers. The upper-corner Jacobian is absorbed into the Haar
measure \(\nu\), and \(c\) records the group Haar normalizations.
