# Conjugation of the compact subgroup in the Levi pairing

Let \(P_J=M_JU_J\) be a standard parabolic of a compatible family, and let
\(K\) be a maximal compact with \(P_J(\mathbb A)K=G(\mathbb A)\). For an
infinite adelic point embedded as \(t\in G(\mathbb A)\), put
\(K'=tKt^{-1}\) and \(R(t)f(g)=f(gt)\).
`leviPairingCompactTranslation` proves `LeviPairingCompactTranslationStatement`.
It carries each square-integrable inducing form for \(K\) to one for \(K'\)
by \(R(t)\). For any \(\psi\) left invariant under \(U_J(\mathbb A)M_J(F)\),
if \(R(t)\psi\) has integrable vanishing pairings against all inducing forms
for \(K'\) at all positive split-component slices, then \(\psi\) has the
corresponding pairings for \(K\).

Iwasawa factorization writes \(t=p k_0\). Decompose \(p\) into Levi and
unipotent factors and write its Levi factor as \(s b\) with \(s\) in the
positive split centre and \(b\) of norm one. The image \(y\) of \(s\) in
\(P_J(\mathbb A)\) belongs to the positive split component in the standard
family. At a slice \(x\) for \(K'\), the evaluation of a translated
left-invariant function equals evaluation of the original function at
slice \(xy\) for \(K\), with coordinates changed by
\[
  (k',m)\longmapsto (k_0t^{-1}k't,\;m b).
\]
The positive central factor commutes with the Levi representative. Normality
moves the unipotent factor to the left, where it acts trivially on the
function. Invariance under the rational Levi points makes this formula
valid with the representatives chosen by the Library. The compact map
preserves Haar probability by conjugation and left invariance. The Levi map
preserves the norm-one quotient Haar measure by right invariance. Their
product gives an exact change of variables for the pairing integrand.

To check the inducing norm, the canonical norm-one quotient homeomorphism
pulls the modulus-weighted squared norm on the split-centre quotient back
to the ordinary squared norm on the norm-one quotient. The representative
change is allowed by the left invariance of the modulus-weighted kernel.
At the identity slice for the translated form, the change of variables gives
the original form at \(y\). Its positive split-component equivariance gives
a fixed squared half-modulus factor times the squared norm at the identity
slice. This proves integrability. Infinite right translation gives the
conjugated compact in the automorphy condition and commutes with the left
split-component action.

For orthogonality at a prescribed original slice \(x\), test the translated
inducing form at \(xy^{-1}\) for \(K'\). The change of variables transfers
both the absolute convergence and the zero value of this pairing to the
original slice. The pairing here is the integral in Delorme's (3.7) before
its external inverse-modulus factor, as in `IsSquareIntegrableOrthogonal`.

The slice and split-component conventions are from P. Delorme,
*On the spectral theorem of Langlands*, Advances in Mathematics 426 (2023),
109107, §2, pp. 5–6 and §3.4, p. 15. The source uses a chosen compact.
The change of compact above follows from the Iwasawa and Haar identities
for the actual groups. The published PDF in
`delorme-2023-spectral-theorem-langlands` has SHA-256
`9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`.
