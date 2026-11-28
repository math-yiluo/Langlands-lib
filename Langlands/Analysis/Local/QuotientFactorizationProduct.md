# Product integration on compatible left quotients

Let \(j\colon M\to G\) be a continuous group homomorphism. Suppose that
\(J\le M\) and \(H\le G\) are closed subgroups and that an isomorphism
\(e\colon J\to H\) agrees with \(j\) on \(J\). For a continuous map
\(k\colon X\to G\), `quotientFactorizationProductMap` sends
\[
 (Jm,x)\longmapsto H j(m) k(x).
\]
This is well defined because \(j(J)\subseteq H\). The product of the open
quotient map \(M\to J\backslash M\) and the identity of \(X\) shows that
this map is continuous.

Suppose the subgroup measures correspond by \(e\). Let \(\nu_M\) and
\(\nu_G\) be compatible quotient measures for the given group and subgroup
measures. If \((m,x)\mapsto j(m)k(x)\) sends \(\mu_M\times\rho\) to
\(c\mu_G\), `IsCompatible.map_quotientFactorizationProduct` shows that the
quotient map above sends \(\nu_M\times\rho\) to \(c\nu_G\). The result uses
locally compact Hausdorff second-countable groups with Borel measurable
structures, Borel structures on the second-countable parameter space
\(X\) and both left quotients, group and subgroup measures finite on
compact sets, right-invariant subgroup measures, and an s-finite
parameter measure \(\rho\). It also takes a measurable normalizing
function \(r\colon G\to[0,\infty]\) satisfying
\(\int_H r(hg)\,d\mu_H(h)=1\) for every \(g\).

For a nonnegative measurable test function \(f\) on \(H\backslash G\), the
proof lifts \(f\) to \(g\mapsto f(Hg)r(g)\). For fixed \(x\), apply the
measurable Weil formula on \(M\) to the lifted function composed with
\(m\mapsto j(m)k(x)\).
The test function is constant on each \(J\)-coset, and \(e\) transports the
integral of \(r\) on that coset to its normalized \(H\)-integral. Tonelli's
theorem and the assumed group pushforward then give \(c\) times the integral
of the lift on \(G\). The Weil formula on \(G\) recovers the integral of \(f\)
against \(c\nu_G\). Indicator tests give the measure equality.

In *Admissible invariant distributions on reductive \(p\)-adic groups*,
§1.2, proof of Lemma 1.5, printed p. 7, Harish-Chandra uses the same Haar
measure on \(A_\Gamma\), the split component of the Cartan \(C_\Gamma\),
to normalize the measures on \(G/A_\Gamma\) and \(M/A_\Gamma\).
Inversion carries these right quotients to left quotients and changes
the factorization order from \(knm\) to \(m^{-1}n^{-1}k^{-1}\), with the
unipotent and compact factors forming the parameter. The general
compatible-quotient formula also applies to the full stabilizers in
orbital descent. The scalar keeps track of the choice of Haar measures.
