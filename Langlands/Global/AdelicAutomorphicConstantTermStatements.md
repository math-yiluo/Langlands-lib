# Automorphy of nested constant terms and finite exponent decompositions

The module `Langlands.Global.AdelicAutomorphicConstantTermStatements` states two
propositions about automorphic functions on the parabolic quotients
\(U_P(\mathbb A) M_P(F)\backslash G(\mathbb A)\) of a compatible family of
standard parabolics. It states them and does not prove them.

## Common data

Both statements quantify over the following, which is the data of
`TemperedWeakConstantTermVanishingStatement` (module
`AdelicTemperedVanishingReduction`) without its differential commutator
`hcalc`:

- a number field `F : Type` and an affine group scheme `G` over `F`, locally of
  finite type, with `IsConnectedReductive G`;
- a subgroup `K` of the adelic points \(G(\mathbb A)\) with
  `IsMaximalCompactSubgroup F G K`;
- a matrix representation `rho : MatrixRepresentation G (Fin N)` with
  `IsClosedSubgroup rho`, whose adelic norm is the growth norm;
- a smooth structure `hsmooth : SmoothOfRelativeDimension d G.X.hom`;
- a compatible family `𝓕 : StandardParabolicFamily F G` with
  `IsIwasawaCompact (𝓕.p 𝓕.bot) K`, that is
  \(P_\emptyset(\mathbb A) K = G(\mathbb A)\) for the minimal standard
  parabolic \(P_\emptyset\).

Automorphy is `𝓕.IsAutomorphicOn hsmooth Kinf rho P` with
`Kinf = K.comap (ofInfinite F G).toMonoidHom`, the subgroup
\(K_\infty = K\cap G(\mathbb A_\infty)\). This is
`IsAutomorphicFunctionOn` (module `Langlands.Automorphic.GroupSchemeInvariantForms`)
for the subgroup `AdelicGroupPoints.parabolicQuotientSubgroup`, the join of the
images of \(U_P(\mathbb A)\) and \(M_P(F)\), which is \(U_P(\mathbb A) M_P(F)\).
It asks for left invariance under this subgroup, smoothness,
\(K_\infty\)-finiteness, finiteness under the centre of the enveloping algebra,
and moderate growth for the norm of `rho`. `IsAutomorphicOn` fixes its
differential commutator as the theorem
`Langlands.Automorphic.GroupSchemeFunctions.adelicDifferentialCommutator_of_smooth`,
so a commutator hypothesis would add nothing to the statements. These are the automorphy conditions that
`StandardParabolicFamily.IsWeakConstantTerm` uses in
`TemperedWeakConstantTermVanishingStatement`.

Every maximal compact `K` with \(P_\emptyset(\mathbb A)K = G(\mathbb A)\) is
allowed. This includes finite-place components that are not in good position
with respect to a minimal Levi subgroup; see "The compact subgroup" in
`AdelicTemperedVanishingReduction.md`. `K` enters the conclusions only through
\(K_\infty\). Since `K` is maximal compact, it is the product of its projections
to \(G(\mathbb A_\infty)\) and \(G(\mathbb A_f)\). Hence \(K_\infty\) is a
maximal compact subgroup of \(G(\mathbb A_\infty)\), as in the sources.

## `AdelicStandardConstantTermAutomorphyStatement`

For standard indices `Q ≤ P`, let `f` satisfy `𝓕.IsAutomorphicOn hsmooth Kinf rho P f`.
Then `𝓕.constantTerm Q f` satisfies `𝓕.IsAutomorphicOn hsmooth Kinf rho Q`. The
index order is containment of the parabolics (`StandardParabolicFamily.le_iff_range_le`).

The function `𝓕.constantTerm Q f` is the Library's ordinary constant term along
\(Q\), with no restriction to \(P\):
\[
  f_Q(g) = \int_{U_Q(F)\backslash U_Q(\mathbb A)} f(ug)\,du ,
\]
for the normalized quotient Haar measure (`subgroupConstantTerm`), with `f`
evaluated at chosen representatives. Since \(Q\subseteq P\), the rational points
\(U_Q(F)\subseteq P(F) = M_P(F)U_P(F)\) lie in \(U_P(\mathbb A)M_P(F)\). So the
input invariance makes the integrand independent of the representatives.

Mathematical origin. Mœglin–Waldspurger I.2.6 (p. 27) shows that the constant
term of a function on \(U(F)\backslash G(\mathbb A)\) is left invariant under
\(M(F)\) when the function is left invariant under \(G(F)\). It has moderate
growth, or is smooth, when the function has that property. I.2.17 (pp. 37–38) defines automorphic forms on
\(U(\mathbb A)M(F)\backslash G(\mathbb A)\) and reduces them to automorphic forms
on the Levi \(M\). Delorme, §3.1 (p. 9), states the nested case: for \(Q\subset P\)
and \(\varphi\in\mathcal A_P(G)\), \(\varphi_Q\) is a well defined element of
\(\mathcal A_Q(G)\).

The nested structure is Delorme (3.6) (p. 14), up to the normalizing factors
of (3.5). The radical splits as \(U_Q = (U_Q\cap M_P)\,U_P\), with \(U_P\) normal
in \(P\), and the input is left invariant under \(U_P(\mathbb A)\). So for each
\(k\in K\) the function \(m\mapsto f_Q(mk)\) on \(M_P(\mathbb A)\) is the ordinary
constant term inside the Levi \(M_P\), along its standard parabolic
\(Q\cap M_P\), of \(m\mapsto f(mk)\). The function \(f_Q\) is left invariant under
\(U_P(\mathbb A)\subseteq U_Q(\mathbb A)\). Also \(G(\mathbb A) =
U_P(\mathbb A)M_P(\mathbb A)K\), since \(P_\emptyset\subseteq P\). So these Levi
constant terms determine \(f_Q\) on the ambient group.

## `AdelicAutomorphicExponentDecompositionStatement`

For every standard index `P` and every `ψ` with `𝓕.IsAutomorphicOn hsmooth Kinf rho P ψ`
there are a finite set `s : Finset (ComplexCharacterParameter F (𝓕.P P))` and
functions `c` with
`𝓕.IsAutomorphicExponentDecomposition hsmooth Kinf rho P ψ s c`. This means:

- \(\psi = \sum_{\lambda\in s} c_\lambda\);
- every \(c_\lambda\), \(\lambda\in s\), satisfies `𝓕.IsAutomorphicOn hsmooth Kinf rho P`
  for the same \(K_\infty\), `rho` and `hsmooth`;
- every \(c_\lambda\) satisfies `𝓕.HasExponent P λ`. There is an `n` such that for
  every \(g\) some polynomial \(p_g\) of degree at most `n` on
  \(\mathfrak a_P\) (`polynomialFunctions`) gives
  \(\delta_P(a)^{-1/2}c_\lambda(ag)\,a^{-\lambda} = p_g(H_P(a))\) for all
  \(a\) in the positive split component \(\mathfrak A_P\)
  (`positiveSplitComponent`), that is \(c_\lambda(ag) = a^{\lambda+\rho_P}p_g(H_P(a))\).

The labels are complex parameters \(\lambda\in\mathfrak a_{P,\mathbb C}^* =
\mathbb C\otimes X^*(P)\), and they are distinct as elements of a finite set.
The exponents are normalized. By `StandardParabolicFamily.hasExponent_iff`,
`HasExponent P λ` is `HasUnnormalizedExponent P (λ + ρ_P)`, with \(\rho_P\) the
half-modulus parameter. The statement asserts existence only. Terms may vanish,
and uniqueness is not part of it. The theorem
`StandardParabolicFamily.eq_zero_of_sum_eq_zero_of_hasUnnormalizedExponent`
(module `AdelicLeadingExponentDirectness`) proves that such sums are direct.

Mathematical origin. In Delorme (3.2) (p. 10), every \(\varphi\in\mathcal A_P(G)\)
is written uniquely as
\(\varphi(g)=\sum_{\lambda\in\mathcal E_P(\varphi)} e^{\lambda(H_P(g))}\varphi_{0,\lambda}(g)\)
with \(\varphi_{0,\lambda}\in S(\mathfrak a_P^*)\otimes\mathcal A^n_P(G)\). Here
\(\mathcal A^n_P(G)\) consists of the forms with
\(\varphi(\exp X g) = e^{\rho_P(X)}\varphi(g)\). The term of \(\lambda\) is
\(c_\lambda\) above, with the same normalized label \(\lambda\).

Mœglin–Waldspurger I.3.1–I.3.2 (pp. 40–43) prove the decomposition.
I.2.17 shows that an automorphic form on
\(U(\mathbb A)M(F)\backslash G(\mathbb A)\) is finite for the centre of the
enveloping algebra of \(M\) acting by left translation. This uses the
Harish-Chandra homomorphism and the finiteness of that centre over its image. In
particular the form is finite for the enveloping algebra of the real split
component. By I.3.1 its left translates along \(\mathfrak A_P\) are then finite
sums of characters times polynomials in \(\log a\). The proof of the Lemma of
I.3.2 shows that the coefficient functions \(\psi_{\mu,q}\) of its formula (2) are
automorphic. These are indexed by characters \(\mu\) of the split component and
basis polynomials \(q\). The characters there are unnormalized. Grouping the
terms by \(\mu\) and setting \(a = 1\) gives the summand with normalized label
\(\lambda = \mu - \rho_P\):
\(c_\lambda(g) = \sum_q m_P(g)^\mu q(\log m_P(g))\,\psi_{\mu,q}(g)\).
It is automorphic by the first paragraph of I.3.2. Mœglin–Waldspurger further
decompose by characters of the centre \(Z_M\). That refinement is not part of
this statement.

## Use

Let `φ` satisfy `IsAutomorphicOn` at `P` and let `Q ≤ P`. Applying the first
statement and then the second, to `𝓕.constantTerm Q φ`, gives a decomposition
of that constant term. Its unitary part is a weak constant term of `φ` along
`Q` in the sense of `StandardParabolicFamily.IsWeakConstantTerm` (Delorme,
Definition 3.7, p. 13, and Lemma 3.8, p. 14), for the same \(K_\infty\), `rho`
and `hsmooth`.

## Sources

- C. Mœglin and J.-L. Waldspurger, *Spectral Decomposition and Eisenstein
  Series*, Cambridge University Press, 1995: I.2.6 (p. 27), I.2.17
  (pp. 37–38), I.3.1–I.3.2 (pp. 40–43).
- P. Delorme, *On the spectral theorem of Langlands*, Adv. Math. 426 (2023),
  109107: §3.1 (p. 9), (3.2) (p. 10), (3.6), Definition 3.7 and Lemma 3.8
  (pp. 13–14).
