# Rectangular unipotent Fourier identity

The theorem `Langlands.HarmonicAnalysis.adjacentRankUnipotentFourier` proves
exactly the published closed proposition
`Langlands.HarmonicAnalysis.AdjacentRankUnipotentFourierStatement.{uF}`.
It retains every prime, every finite extension of the corresponding p-adic
field in universe `uF` with its canonical topology and Borel structure, every
supplied nontrivial continuous unitary additive character `psi`, scalar additive
Haar measure `nu` and certificate `IsSelfDual psi nu`, every natural `r` including
zero, and every Schwartz–Bruhat function `Phi` on `(r+1)` by `(r+2)` matrices.
Both complex integrands are integrable and their Bochner integrals agree for
the same prescribed `RankinSelberg.unipotentHaar F.Carrier r`.

Write `n=r+1`, `w=w_n`, `epsilon` for the last standard basis column,
`zeta=diag(-1,...,-1,1)`, `T` for inverse-character last-column Fourier,
and `H` for full plus-character Fourier, using the supplied products of `nu`.
The two integrands proved equal after integration are exactly

```text
L(u) = T(rectangularTranslate(w_(n+1)*zeta) Phi)([u,epsilon]) theta(u)^(-1)
R(u) = H(T Phi)([w*u,w*epsilon]) theta(u),
```

where brackets mean the actual `rectangularJoin`, ordinary right translation
means `Phi(m*g)`, and `theta` is `Whittaker.standardCharacter psi r`.

The source context is Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg
Convolutions* (1983), registered as `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The identity is Section 6.2, Lemma (2), printed page 431, with the Fourier
inversion reduction (3) on pages 431–432. Section 6.1, pages 427–428, supplies
the right action and Fourier conventions. The implemented proof uses the
Library's complementary affine Fourier identity to realize this reduction.
The two convergence assertions are the derived strengthening specified in the
published target.

Put `b=w*epsilon` and let `f(A)=Phi([A,b])`, the actual Schwartz function
`rectangularFixedLastColumn b Phi`. The private left expansion opens the
last-column Fourier integral and moves the fixed inverse character into it.
The actual matrix identity `adjacentRankLeftMatrix_join` identifies the input
with `[A(u,y),b]`, where the first column of `A` is `-y` and its other columns
are the reversed, negated noninitial columns of `u`. Its antidiagonal sum is
`-y(last r)-unipotentFourierSum r u`. The additive-character multiplication
and negation formulas therefore give exactly the original two character
factors, with every sign retained.

For the right expansion,
`rectangularFourierEquiv_partial_fixedLastColumn` cancels full plus Fourier
against the inverse-character partial Fourier on the final column. This leaves
square plus Fourier of `f` at `w*u`. The actual shifted antidiagonal sum there
is `unipotentFourierSum r u`, hence its character is the standard character.
The cancellation helper uses scalar self-duality and finite tensor decomposition
to cover arbitrary `Phi`.

`adjacentRankAffine_fourier_duality` equates the integral of square Fourier of
`f`, weighted by its shifted antidiagonal character on the right affine slice,
with the integral of `f`, weighted by its antidiagonal character on the
complementary left slice. It also supplies both integrability conclusions.
`adjacentRankRightParam_preserving` and
`adjacentRankLeftParam_preserving` pull these exact slice measures back to the
strict-upper-coordinate product and, on the left, its product with a full row.
Their entry formulas identify the pullbacks with `w*u` and `A(u,y)`.
Integrability of the left pullback justifies Fubini, producing equality of the
coordinate integrals of `L` and `R`.

`GeneralLinear.exists_upperEntry_integral` then compares an arbitrary actual
upper-unipotent Haar with the coordinate product by a single positive real
scalar. Applying its integral formula to both integrands multiplies the
coordinate equality by the same scalar. The proof never sets this scalar to
one and does not identify the normalized group Haar with the supplied product.
The generic bridge uses a Hausdorff locally compact totally disconnected,
second countable Borel topological field and sigma-finite scalar Haar. In the
closed target these properties follow from the canonical p-adic data and
`selfDualSigmaFinite`; none is an extra premise of the theorem.

Finally, `adjacentRankUnipotent_integrable` supplies the two literal convergence
conjuncts. Its proof restricts the transformed Schwartz functions along the
closed embeddings `u -> [u,epsilon]` and `u -> [w*u,b]`, then multiplies by the
continuous standard or inverse character. Compact support gives integrability
for every measure finite on compact sets, including the prescribed group Haar.
This completes all three conjuncts. No representation or model coefficient,
factorization of `Phi`, growth condition or additional measure compatibility
is assumed. Worker 1198 implemented the Fourier bridge; Worker 86 contributed
the actual matrix and convergence helpers used in it.
