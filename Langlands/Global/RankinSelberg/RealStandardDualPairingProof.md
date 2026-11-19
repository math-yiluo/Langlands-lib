# Dual-block pairing for real standard modules

`Langlands.Global.RankinSelbergGlobal.realStandardDualPairing`, in module
`Langlands.Global.RankinSelberg.RealStandardDualPairingProof`, proves
`RealStandardDualPairingStatement` from [RealStandardPairingPremises](RealStandardPairingPremises.md).
It gives a complex bilinear form invariant under \(O(n)\) and the real Lie algebra directions,
with zero right kernel. The construction works for every list of total rank \(n\). The theorem
retains the irreducibility premise of the published statement.

## Construction

Write \(I(ds)\) for the compact-finite standard module. Set `es = ds.flatMap repl` and
`dual = ds.map dualBlock`. The Library's `RealTemperedForm.repl` replaces each induced block of
nonzero weight \(m\) and exponent \(t\) with two characters, in the order with exponents
\(t-|m|/2\) and \(t+|m|/2\). It preserves the position signs and keeps the zero-weight blocks and
the character blocks. The proof computes that the position signs of `es` and `dual` agree and
their exponents are opposite. Their position characters are therefore pointwise inverse.

The Fourier multiplier chain `RealTemperedForm.chain` supplies a linear map
\(T : I(es) \to I(ds)\) commuting with the real Lie algebra action and a linear right inverse
\(S : I(ds) \to I(es)\) commuting with \(O(n)\). The pairing is
\[
Q(f,h)=\int_{O(n)} (S f)(k)\,h(k)\,dk .
\]
It is the Library's `RealPrincipalSeriesDuality.pairing` precomposed with \(S\) in its first
argument. Haar invariance and equivariance of \(S\) give the compact group identity.

## Lie invariance and separation

For each \(h \in I(\mathrm{dual})\), the proof constructs \(g \in I(ds)\) with
\(g(k)=\overline{h(k)}\) on \(O(n)\). Dualization preserves the sign-reflection characters, which
are real, and the absolute weights of the induced blocks. The compact extension
`RealLeviModes.exists_ext_conj` supplies the conjugate restriction in the original principal
series. Compact conjugation sends a rotation mode \(j\) to \(-j\), so the conjugate restriction
satisfies all the original Fourier windows. The Library lemma
`RealBlockPosition.mem_realStandardModule_of_unitaryCompact` then supplies standard-module
membership.

If \(Tw=0\), the Library's orthogonality lemma
`RealTemperedForm.integral_mul_conj_eq_zero_of_ker` gives
\(\int_{O(n)}g(k)\overline{w(k)}\,dk=0\). Conjugating gives
\(\int_{O(n)}w(k)h(k)\,dk=0\). For a real matrix \(X\), the difference \(S(Xf)-X(Sf)\) lies in
\(\ker T\). Thus the Lie identity for \(Q\) follows from
`RealPrincipalSeriesDuality.pairing_rightDerivative` at \(Sf\) and \(h\), using the inverse
position characters.

For separation, choose \(f\) with compact restriction \(\overline h\). If \(Q(f,h)=0\), its
conjugate is \(\int_{O(n)} f(k)\overline{(Sf)(k)}\,dk=0\). The anisotropy lemma
`RealTemperedForm.eq_zero_of_integral_mul_conj` gives \(f=0\), so \(h\) vanishes on \(O(n)\).
Compact restriction is injective on the principal series by Iwasawa decomposition, giving \(h=0\).

## Provenance

This is a derived proof for the Library's Fourier-cutoff model. The compact integral is the
normalized-induction pairing associated with Knapp's compact integral formula in
*Representation Theory of Semisimple Groups* (1986), Chapter VII, §2, equation (7.4), p. 170
(`provided-40cace9c0f8c2361e7b3d7459f7908362f819b68114945405f1c16d968b21855`).
The implemented descent and separation use the Library Fourier multiplier lemmas described above.

Knapp presents the real building blocks and their normalized induction in (2.2) and (2.4),
p. 400 (`knapp-1994-archimedean-llc`).
[*Local Langlands Correspondence: The Archimedean Case* (1994)](https://www.math.utah.edu/~ptrapa/math-library/knapp/knapp-LLC-gln.pdf)
