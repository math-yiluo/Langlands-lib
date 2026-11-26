# Hodge–Tate comparison for proper smooth schemes

Gerd Faltings, *p-adic Hodge theory*, J. Amer. Math. Soc. 1 (1988), 255–299,
states the comparison in Chapter III, Theorem 4.1, printed p. 298 (PDF
p. 45). The proper smooth formula in §1(b), printed p. 255 (PDF p. 2),
pairs \(H^a(X,\Omega^b_{X/K})\) with twist \(-b\). Section 1(c) repeats
this convention on printed p. 256 (PDF p. 3). The formula on p. 298
prints \(-a\) while leaving the superscripts on \(H^a\) and \(\Omega^b\)
in the same order. The statement uses the twist \(-b\) of the introduction,
that is, minus the differential-form degree. Registered source ID
`provided-1991b7d5032d5fe94ca932ccbeccf293bafd80aa29a350ed2fda545cf46b9440`,
SHA-256 `2eb8b02f9e3e7662e1e79229488ee7e98240e23f221f1c9aaa7bec79cf329024`.

Theorem 4.1 asserts naturality. The preceding paragraph of III §4(b),
also on printed p. 298, treats pullback by factoring a morphism through
its graph and the projection. The case here takes the divisor to be empty.

## Lean proposition

`Langlands.Cohomology.HodgeTate.ProperSmoothHodgeTateNaturalStatement`
fixes the finite extension \(K/\mathbb Q_p\) and the degree \(q\).
It asserts a simultaneous family of Galois-equivariant linear
comparisons, one at each proper smooth scheme over \(K\), that commutes
with pullback along every morphism over \(K\). The geometric-sheaf and
coefficient-module derived-category universes are independent.
The geometric-sheaf universe is fixed across the family.
`properSmoothHodgeTateStatement_of_natural` evaluates such a family to
give the objectwise proposition.

`Langlands.Cohomology.HodgeTate.ProperSmoothHodgeTateStatement` concerns
the smooth proper morphism \(X\to\operatorname{Spec}K\) for a finite
extension \(K/\mathbb Q_p\). Let \(C_K=\widehat{\overline K}\) with the
spectral norm. For each cohomological degree \(q\) the proposition
asserts a \(C_K\)-linear isomorphism intertwining the semilinear Galois
actions

\[
 \bigoplus_{j=0}^{q} C_K(-j)\otimes_K
       H^{q-j}(X,\Omega^j_{X/K})
 \;\cong\;
 C_K\otimes_{\mathbb Q_p}H^q_{\mathrm{et}}(X_{\overline K},\mathbb Q_p).
\]

The finite product indexed by `Fin (q + 1)` represents the sum. In term
`j`, a Galois element `σ` acts by applying its extension to \(C_K\) on the
first tensor factor and multiplying by \(\chi_p(\sigma)^{-j}\). The coherent
cohomology over \(K\) has the trivial group action. On the étale side
the action is that on \(C_K\) tensored with the actual cohomology action.
The completion \(C_K\) uses the spectral norm on \(\overline K\)
extending the \(p\)-adic norm on \(\mathbb Q_p\).

The construction uses `EtaleSchemeDeckAction.cohomologyFunctor` for the
Galois automorphisms of the algebraic-closure factor of
`EtaleGaloisAction.baseChange`. Its inputs are the constant sheaves
`ℤ_p/p^m` on \(X\), pulled back to \(X_{\overline K}\). The constant-sheaf
inverse-image comparison identifies them with the same constant sheaves
on \(X_{\overline K}\). The construction takes the inverse limit of
cohomology and then extends scalars from `ℤ_p` to `ℚ_p`. The sheaf and
module derived-category universes are independent.

The coherent cohomology uses `DerivedSections.relativeCohomology` on
`differentialForms`. This sheaf is obtained by applying the exterior
power of modules over each ring of sections of \(\mathcal O_X\) to the
sheaf of relative Kähler differentials and sheafifying. On restrictions
the defining alternating map wedges the restricted entries. The identity
and composition laws follow on wedge generators.

`ellAdicEtalePullback` uses the actual map of geometric schemes.
The isomorphism for inverse images of constant sheaves compares the
underlying diagram of the Galois cohomology construction with the
diagram of constant-coefficient cohomology on the geometric scheme.
The finite-stage pullbacks give the map of limits, which is extended
to \(\mathbb Q_p\). `hodgeCohomologyPullback` uses the canonical pullback
of relative coherent cohomology and the pullback map of differential
forms. That coefficient map wedges the maps on relative Kähler
differentials, applies the sheafification unit, and uses the adjunction
for pullback of scheme modules. The equation in the natural proposition
asserts that the comparison intertwines the extensions of these two
maps to \(C_K\).

## Application to algebraic coefficients

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), proof of Theorem 5.7(i), printed pp. 313–314 (PDF pp. 15–16),
uses Hodge–Tate comparison for cohomology with general algebraic
coefficients. Those coefficient systems arise from tensor powers of the
cohomology of the universal abelian scheme. The comparison here is
natural on the proper smooth constant-coefficient schemes used in that
argument. In particular, naturality and linearity intertwine a projector
expressed as a linear combination of pullbacks of scheme endomorphisms
and identify its two images after extension to \(C_K\).
The realization of the algebraic coefficient system by a specific
projector and compatibility with trace maps in Hecke correspondences
are additional inputs to labelled cohomology.
The registered Harris original is
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
