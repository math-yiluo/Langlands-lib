# Isometric lifting by an ambient wave-packet profile

`Langlands.Global.ambientProfileL2Isometry` maps
\(L^2([G],\texttt{canonicalMeasure})\) into
\(L^2(G(F)\backslash G(\mathbb A_F),\texttt{rationalQuotientHaarMeasure})\).
It uses the actual connected reductive group over a number field and
the Library's canonical split-centre quotient, in universe zero. The
ambient chart \(e_G\) and the nonzero smooth compactly supported
coefficient \(b\) determine the existing Fourier profile \(B\).
In the quotient coordinates \((a,y)\in A_G\times[G]\), the map takes the
class of \(f\) to the class represented by

\[
 (a,y)\longmapsto \frac{B(a)f(y)}
   {\sqrt{\displaystyle\int_{A_G}|B(a')|^2\,da'}}.
\]

The Haar measure in the denominator is `positiveCentreHaarMeasure`.
This measure times the canonical quotient measure is the actual measure
of the full rational quotient in product coordinates. The established
discrete quotient product law and its adelic specialization give the
measure equality. Projection onto the second coordinate is
quasi-measure-preserving, which allows the additivity and scalar laws
for the representatives to descend to \(L^2\) classes. The ambient
profile pairing supplies square integrability, the positive squared
norm of \(B\), and the scaling of the unnormalized inner product.
Dividing by that norm gives a complex linear isometry.

The construction gives a normalized Hilbert-space map for the central
profile comparison between the full parameters in Lapid (2011),
§3, Proposition 2, printed p. 314 (PDF p. 323), and the relative
parameters in Getz–Hahn (2024), §10.5, (10.22)–(10.24), printed
pp. 281–282 (PDF pp. 293–294). The product quotient uses Getz–Hahn
§2.6, (2.19)–(2.22) and Lemma 2.6.2, printed pp. 68–69
(PDF pp. 85–86). The normalization by the profile norm is a derived
construction for these exact Library measures.
