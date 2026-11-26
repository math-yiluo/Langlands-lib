# The uniform cuspidal expansion for finite families from three named inputs

Module `Langlands.Global.AdelicEisensteinUniformCuspidalExpansionReductionStatement` states the
proposition `Langlands.Global.EisensteinUniformCuspidalExpansionReductionStatement` (universe
`u`) and proves nothing.

## Statement

`EisensteinUniformCuspidalExpansionReductionStatement` is the implication

`ConstantTermAutomorphyStatement → AutomorphicExponentDecompositionStatement →
LeviCuspFormRapidDecayStatement → EisensteinUniformCuspidalExpansionStatement`,

all at universe `u`.

The conclusion (module `AdelicEisensteinUniformCuspidalExpansionStatement`) is the identity case
(6.21) of Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math.
Soc. 37 (2024), Corollary 6.10, §6.10, pp. 208–209, read in the norm-one Levi cusp tests (6.8) of
§6.2, p. 202. Fix finitely many automorphic inducing functions \(\varphi_1,\dots,\varphi_m\) on
\(U_I(\mathbb A)M_I(F)\backslash G(\mathbb A)\) and a standard index \(J\). Then there are a
threshold \(R\), competing labels of the identity Weyl element (`CompetingWeylExponents fam I J 1`)
and a degree bound \(n\), chosen before the parameter and the coefficients, with the following
property. For every \(R\)-regular \(\lambda\) and all coefficients \(a_1,\dots,a_m\) there are terms,
each with the unnormalized exponent given by its label at \(\lambda\) and polynomial degree at
most \(n\) (`HasPolynomialOrbit`), such that for every norm-one Levi cusp test on \(M_J\) and every
base point \(g\):

- each term is integrable against the test on the norm-one quotient of \(M_J\);
- the tested value at \(g\) of the constant term along \(J\) (`constantTerm J`) of
  \(\sum_ia_iE(\varphi_i,\lambda)\), minus the tested value at \(g\) of
  \(C_{I,J}\bigl(\sum_ia_i\varphi_{i,\lambda}\bigr)\), is the sum of the tested values of the terms.

Here \(C_{I,J}\) is `parabolicConstantTerm I J`: the constant term along \(J\) when \(J\le I\) and
\(0\) otherwise, the convention of Bernstein–Lapid §6.2, p. 201.

The three premises are the Library propositions:

- `ConstantTermAutomorphyStatement` (module `AdelicConstantTermAutomorphyStatement`): the
  constant term along a standard \(Q\le P\) of an automorphic function on
  \(U_P(\mathbb A)M_P(F)\backslash G(\mathbb A)\) is automorphic on
  \(U_Q(\mathbb A)M_Q(F)\backslash G(\mathbb A)\) (Bernstein–Lapid §6.2, p. 201);
- `AutomorphicExponentDecompositionStatement` (module
  `AdelicAutomorphicExponentDecompositionStatement`): an automorphic function on
  \(U_Q(\mathbb A)M_Q(F)\backslash G(\mathbb A)\) is a finite sum of automorphic functions with
  generalized unnormalized exponents, cuspidal when the input is (Bernstein–Lapid (6.3), (6.6),
  (6.10); Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995), I.3.2);
- `LeviCuspFormRapidDecayStatement` (module `AdelicLeviCuspFormRapidDecayStatement`): cusp forms
  on the standard Levis are rapidly decreasing on norm-one representatives (Mœglin–Waldspurger
  I.2.12, I.2.18).

The integration identity of the geometric lemma in the proof of Bernstein–Lapid Lemma 6.10 is not
a premise: it is the Library theorem `geometricLemmaUnfolding` (module
`EisensteinConstantTerm.GeometricLemmaUnfoldingProof`).

## Provenance

Derived; this implication is not stated in the cited sources. It isolates the analytic inputs of
the argument of Bernstein–Lapid §6.10 for Corollary 6.10.

By Lemma 6.10, (6.17), the constant term \(C_{G,J}E(\varphi,\lambda)\) is the sum over
\(w\in{}_J W_I\) of Eisenstein series of \(M(w,\lambda)C_{I,I_w}\varphi\); this rests on the
integration identity of the geometric lemma and on the absolute convergence of Eisenstein series.
Its cuspidal projection (6.18) is the sum over the Weyl indices with target Levi \(M_J\) of the
twisted terms \([M(w,\lambda)\,C^{\mathrm{cusp}}_{I,I_w}\varphi]_{w\lambda}\).

For a generalized eigencomponent of \(C^{\mathrm{cusp}}_{I,I_w}\varphi\) with normalized exponent
\(\mu\) along \(P_{I_w}\), (6.4) transports \(\mu\) to \(w\mu\) before the twist, so the normalized
exponent of the twisted term is \(w(\mu+\lambda|_{P_{I_w}})\). The labels of
`HasPolynomialOrbit` are unnormalized, and by (6.10) the corresponding unnormalized label is
\(w(\mu+\lambda|_{P_{I_w}})+\rho_J\); if \(\mu\) denotes instead the unnormalized exponent of the
input component, \(\rho_{I_w}\) is first subtracted from it. By (6.14)–(6.15) the polynomial degree
of the transported term is bounded by the degree of the input component, which does not depend on
\(\lambda\).

In (6.18) and (6.21) the contribution of the identity \(w=e\) is the cuspidal projection
\(C^{\mathrm{cusp}}_{I,J}\varphi_\lambda\). By (6.8) its pairing with a norm-one cusp test equals the
pairing of \(C_{I,J}\varphi_\lambda\), the subtracted term of the conclusion. The absolute
convergence of these pairings uses the rapid decay of the Levi cusp forms.

Constant terms, twists, Eisenstein series in the convergence region and the norm-one pairings are
linear in the inducing function. Taking the largest of finitely many thresholds and degree bounds
and concatenating the competing label lists therefore gives competing labels and one degree
bound for all linear combinations of \(\varphi_1,\dots,\varphi_m\).
