# From the joint continuation of the Eisenstein series to its generic coefficient

Module `Langlands.Global.Factors.CuspidalPairEisensteinHolomorphyReduction`
proves that the joint continuation of the cuspidal-pair Eisenstein series
implies the continuation and the imaginary-axis holomorphy of its generic
coefficient:

```lean
def CuspidalPairEisensteinHolomorphyReductionStatement : Prop :=
  CuspidalPairEisensteinJointContinuationStatement.{u} →
    CuspidalPairEisensteinHolomorphyStatement.{u}

theorem cuspidalPairEisensteinHolomorphyReduction :
    CuspidalPairEisensteinHolomorphyReductionStatement.{u}
```

Both names are in the namespace `Langlands.Global.CuspidalPairEisenstein`. The
premise is
[`CuspidalPairEisensteinJointContinuationStatement`](CuspidalPairEisensteinJointContinuationStatement.md),
which is not proved in the Library. The conclusion is the published S2,
[`CuspidalPairEisensteinHolomorphyStatement`](CuspidalPairEisensteinHolomorphyStatement.md),
at the same universe `u`. So this module does not prove S2; it reduces S2 to
the premise. The reduction uses no other unproved statement, in particular
neither the coefficient factorization S1 nor the boundary nonvanishing theorem.

## Source

Shahidi (1981), proof of Theorem 5.1, p. 352: "by the compactness of
\(U_{\mathbb A}/U_F\) it is clear that the poles of
\(E_\chi(s;\phi;e;P_{\theta,\mathbb A})\) are among those of
\(E(s;\phi;e;P_{\theta,\mathbb A})\), and therefore the theorem follows from the
holomorphy of \(E(it,\phi;e;P_{\theta,\mathbb A})\) for all \(t\in\mathbb R\)".
Here \(E_\chi\) is the generic (Whittaker) coefficient at the identity. The module formalizes this sentence:
it integrates the denominator-cleared family of the premise over the compact
quotient \(N_0(F)\backslash N_0(\mathbb A_F)\) of the upper unitriangular group.
This is step 3 of the route through Mœglin–Waldspurger in the Markdown of S2,
with the holomorphy of the integral proved by differentiation under the
integral sign instead of Morera's theorem.

## The generic coefficient of a function

`genericCoeff n ψ f`, for `f : AdelicGL F (n + 2) → ℂ`, is
`generalLinearWhittakerFunction F (n + 1) ψ (fun _ => 1)` applied at the
identity to `f ∘ adelicEquiv`. That is the integral

\[
  \int_{N_0(F)\backslash N_0(\mathbb A_F)} f(u)\,\overline{\psi_{N_0}(u)}\,du
\]

for the normalized quotient Haar measure, evaluated at the representatives
`Quotient.out`, with value zero if the integrand is not integrable. For
`n = r + t` and `f = eisensteinSeries F φ s` this is `coeff ψ φ s` by
definition; the indexing `n + 2` makes this identification syntactic.

- `genericCoeff_const_mul`: `genericCoeff n ψ (fun g => c * f g) = c * genericCoeff n ψ f`.
  This is `integral_const_mul`, which holds for the Bochner integral whether or
  not the integrand is integrable.
- `differentiableOn_genericCoeff`: let `k : ℂ → AdelicGL F (n + 2) → ℂ` be
  continuous on `W × GL_(n+2)(𝔸)` for an open `W`, complex differentiable in
  `s ∈ W` for each `g`, and left invariant under `AdelicGL.rational` for
  `s ∈ W`. Then `s ↦ genericCoeff n ψ (k s)` is complex differentiable on `W`.
  It assumes `IsStandardAdditiveCharacter F ψ`.

Proof of `differentiableOn_genericCoeff`. Let
\(f(s,u)=k(s,u)\,\overline{\psi_{N_0}(u)}\) on \(W\times N_0(\mathbb A_F)\). It is
continuous: `adelicEquiv` is a homeomorphism (`adelicHomeomorph`) and the
generic character of a continuous \(\psi\) is continuous
(`Unfolding.continuous_genericCharacter`). It is left invariant under
\(N_0(F)\): an element of the rational subgroup is the image of a rational
point, `adelicEquiv_rational` sends it to `AdelicGL.rational`, \(k\) is
invariant, and the generic character is trivial on \(N_0(F)\) because \(\psi\)
is trivial on \(F\) (`Unfolding.genericCharacter_rational_mul`). By
`ImaginaryAxis.continuousOn_out_of_invariant` the integrand
\((s,q)\mapsto f(s,\operatorname{out}q)\) is continuous on \(W\times(N_0(F)\backslash N_0(\mathbb A_F))\).
The quotient is compact (`Unfolding.compactSpace_unipotentRationalQuotient`),
Borel (`rationalQuotientBorelSpace`) and its normalized measure is a
probability measure. For \(s_0\in W\) choose a closed ball of radius \(R>0\)
in \(W\). The integrand is holomorphic in \(s\) on the open ball, so
`MatrixCoefficientAnalytic.hasDerivAt_integral_of_holomorphic` (dominated
differentiation with the Cauchy estimate, in
`Langlands.Representation.Archimedean.PrincipalSeriesMatrixCoefficientAnalytic`)
gives a complex derivative at \(s_0\).

## The reduction

Given the data of S2, the premise gives \(E\), \(\sigma\) and the local data.
Put \(E_c(s)=\) `genericCoeff (r + t) ψ (E s)`.

1. **Right half-plane.** For \(\sigma<\operatorname{Re}s\), `E s = eisensteinSeries F φ s`,
   so \(E_c(s)=\) `coeff ψ φ s` by rewriting and unfolding. No convergence is
   needed for this step.
2. **Meromorphy.** Let \(s_0\in\mathbb C\) with local data \(m,W,h\). Then
   \(H(s)=\) `genericCoeff (r + t) ψ (h s)` is holomorphic on \(W\) by
   `differentiableOn_genericCoeff`, hence analytic at \(s_0\). For
   \(s\in W\), \(s\ne s_0\), `genericCoeff_const_mul` gives
   \(H(s)=(s-s_0)^mE_c(s)\). Mathlib's `MeromorphicAt f s₀` asks for
   analyticity of \(z\mapsto(z-s_0)^n f(z)\) *including its value at
   \(s_0\)*. Take \(n=m+1\): near \(s_0\),
   \((z-s_0)^{m+1}E_c(z)=(z-s_0)H(z)\), both sides being zero at \(z=s_0\).
   So `MeromorphicOn Ec Set.univ`.
3. **Imaginary axis.** For \(s_0=iy\) the premise gives \(m=0\) and
   \(h=E\) on \(W\), including at \(s_0\). So \(E_c=H\) on \(W\), and
   \(E_c\) is analytic at \(iy\).

The proof uses the hypotheses `HasUnitaryCentralCharacter` only to apply the
premise, and of `IsStandardAdditiveCharacter F ψ` only continuity of \(\psi\)
and its triviality on \(F\).

## References

- F. Shahidi, *On Certain L-Functions*, Amer. J. Math. 103 (1981), 297–355:
  proof of Theorem 5.1, p. 352.
- C. Mœglin and J.-L. Waldspurger, *Spectral Decomposition and Eisenstein
  Series*, Cambridge University Press, 1995: IV.1.8, IV.1.9 (c)–(d),
  IV.1.11 (a)–(b), pp. 140–141, for the premise.
