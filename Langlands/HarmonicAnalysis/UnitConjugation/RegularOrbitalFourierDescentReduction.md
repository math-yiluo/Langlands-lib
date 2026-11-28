# Parabolic descent from compact Iwasawa factorization

`RegularOrbitalFourierDescentReduction` is the implication from
`IdempotentParabolicIwasawaStatement` to `RegularOrbitalFourierDescentStatement`.
Both statements retain independent field and algebra universes. For a regular
element \(X\) of a finite-dimensional semisimple local algebra \(A\) lying
in the centralizer \(M\) of an idempotent, the proof uses compact
factorization \(A^\times=PK\) to transfer local integrability of the
Fourier-transformed orbital integral from \(M\) to \(A\).

The proof installs compatible ultrametric norms on the field and
algebra using their given topologies. It restricts the invariant pairing
to \(M\) and obtains two-sided Haar on \(M^\times\) and \(A^\times\).
Regularity identifies the Levi and ambient stabilizers as topological
groups, so transport of ambient stabilizer Haar and the Weil formula give
a compatible Levi quotient measure.

The parabolic orbital measure formula gives an upper-corner Haar and a
positive finite scalar \(c\). It gives absolute convergence of the Levi
orbital integrals and the identity \(\mu_X^M(f_P)=c\,\mu_X^G(f)\) for the
compactly averaged constant term. Normalize additive Haar on \(M\) by the
Fourier commutation formula \((\widehat f)_P=\widehat{f_P}\). Applying the
Levi local integrability hypothesis gives a density \(\theta\) with
\[
 c\,\mu_X^G(\widehat f)
   =\mu_X^M(\widehat{f_P})
   =\int_M \theta(Y)f_P(Y)\,dY .
\]
The locally integrable weighted pushforward in
`IdempotentParabolicAveragedDensity` makes this last expression the pairing
with an ambient density. Division by \(c\) gives the claimed ambient
density.

The result implements the parabolic step of Harish-Chandra's
*Admissible invariant distributions on reductive \(p\)-adic groups*,
§1.2, Lemmas 1.4–1.7, printed pp. 6–8, and §1.4, Lemma 1.13 and
the induction step, printed pp. 10–11. For the orbital measures it uses
left quotients by the full unit stabilizers and retains the corresponding
normalization factor. The density transfer uses the strict submersion on
the conull locus where the off-diagonal adjoint is invertible, with the
support of each test controlling the corresponding weighted integral.
