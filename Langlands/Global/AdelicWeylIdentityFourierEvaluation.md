# Fourier evaluation of the identity Weyl terms

`WeylIdentityFourierEvaluationStatement` uses relative spectral coordinates dual
to the projected simple coroots of the inducing parabolic \(P\). The spectral
measure is additive Haar. Each label \(l\) specifies a parabolic \(Q_l\), a
retraction of \(Q_l\) onto its Levi, and a Weyl representative inducing a
conjugation from the Levi of \(P\) to the Levi of \(Q_l\). Its inverse Weyl
class sends the Levi simple-root set of \(Q_l\) onto that of \(P\).

The truncation ray is \(T_0+kT\), with every simple relative root strictly
positive on \(T\). The tested function is a finite holomorphic ray
representative as in `IsWeylConeRayRepresentative`. At each label with parabolic
\(P\) and identity Weyl class, its holomorphic weight has the constant value
\(\beta_l\) on the relative imaginary slice. The theorem chooses one positive
spectral Haar factor \(C\) for the inducing coordinates before introducing the
ray, frequencies, polynomials and weights.

For each such ray and representative, the theorem gives a finite set of
frequencies and a functional \(D\) depending only on the germs at that set. The
representative integrated against any smooth compactly supported test \(f\)
is eventually absolutely integrable, and the tested integrals converge to
\(C D(f)\). On the phase \(y\mapsto e^{-i\sum_\alpha x_\alpha y_\alpha}\),
the functional is `identityWeylSpatialSum`. At a retained label it contributes
\[
  \beta_l\exp\!\left(-i\sum_{\alpha}
    x_\alpha\langle \nu_l,\alpha^\vee\rangle\right)p_l(x),
\]
using `reindexCorootCoordinates` to identify the coroot indices along the
equality of the two parabolics. The weights can include the factors from the
spatial cone measures.

The proof uses the tested truncation-ray limit with the pushforward identity
for each spectral Haar factor. The ambient Weyl parameter formula makes the
relative spectral chart at an identity label the coroot reindexing. After
substitution along the parabolic equality, this chart is the identity, so
Haar uniqueness gives the same factor for every retained label. Each summand
of \(D\) is the local polynomial evaluation on the test multiplied by its
weight and pulled back by the inverse chart. The finite set consists of the
pullbacks of the corresponding frequency points, which gives the required
germ dependence. For a negative phase, the pulled-back weight is the constant
\(\beta_l\). The polynomial point evaluation uses the formal transpose
\(p_l(-D_y)\), where \(D_{y,\alpha}=i^{-1}\partial_{y_\alpha}\). Acting on the
negative phase gives \(p_l(x)\) times the phase, and evaluation at the coroot
frequency gives the exponential factor above.

This is the identity-class Fourier calculation in the proof of Lemma 7.11 of
Patrick Delorme, *On the spectral theorem of Langlands*, Advances in Mathematics
426 (2023), 109107, printed p. 35. The cone factors and test convention come from
(7.8)–(7.12), pp. 24–25, and the boundary in Proposition 7.8, p. 33. The
transpose is the test-function form of the distributional differentiation in
(7.11). The source `delorme-2023-spectral-theorem-langlands` has folder SHA-256
`e8b15973ea4ddbc7c7ba7f8fdf4eac5b42db2de9f74209baad19948cbfeb517b`.
The file `Delorme--On the spectral theorem of Langlands--2023.pdf` in that
folder has SHA-256
`9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`.
