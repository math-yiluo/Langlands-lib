# Finite-dimensional reduction for the uniform Harish-Chandra equations

`Langlands.Global.InducedHarishChandraFiniteModelStatement` uses the
parabolic, Iwasawa compact and automorphic-form hypotheses of
`InducedHarishChandraEquationsStatement`. At each base character parameter
\(\lambda_0\), it asks for a smooth compact test kernel \(h\) bi-finite under
\(K_\infty\) and a finite-dimensional space \(S\) of continuous functions
containing the original form. For each \(\lambda\), the transported
operator \(T_\lambda^{-1}\delta(h)T_\lambda\) preserves \(S\), where
\(T_\lambda\) multiplies by the Iwasawa height power. Its restriction is
injective at \(\lambda_0\).

`inducedHarishChandraEquations_of_finiteModel` proves the implication to the
exact uniform-equations proposition at arbitrary universe level. It takes
\(\lambda_0=e(s_0)\) and applies
`IsIwasawaCompact.hasConvolutionEquationAt_parameterTwist_of_finiteDimensional`
to the chosen space and kernel. That theorem obtains an entire matrix by
point evaluation and applies Cayley–Hamilton to give the coefficients. The
existence of the invariant space and the injectivity condition are the
premise of this implication.

The premise is a way to isolate the finite-dimensional input to the
characteristic-polynomial argument of Mœglin–Waldspurger, *Spectral
Decomposition and Eisenstein Series*, I.4.5, printed pp. 60–62
(`moeglin-waldspurger-1995-spectral-decomposition`, collection fingerprint
`1ba99fb90916a687503e88c7191dad43b9c4865b68e6b4221a4f2126f2d2f141`,
chapter `05.4_pp_49_77_Upper_bounds_as_functions_of_the_constant_term.pdf`,
SHA-256 `a72fe12ffc7707cc35e91375a8fc9dc62c35570afbbb061c0e7ff6db99a90d3d`).
The source obtains finite-dimensional control on cuspidal components. This
formulation uses a space of functions and transports it by the actual
Iwasawa twist. The conclusion has the entire-coefficient form of
Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*,
§8.3, Lemma 8.3, journal p. 223
(`bernstein-lapid-2024-meromorphic-continuation-eisenstein-published`,
SHA-256 `6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`).
