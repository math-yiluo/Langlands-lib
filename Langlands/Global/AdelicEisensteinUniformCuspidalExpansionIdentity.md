# The identity Weyl element of the uniform convergent cuspidal expansion

Module `Langlands.Global.AdelicEisensteinUniformCuspidalExpansionIdentity`. It defines the
proposition `Langlands.Global.ConvergentCuspidalTestExpansionUniformStatement` and proves

`eisensteinUniformCuspidalExpansionOne_of_uniform : ConvergentCuspidalTestExpansionUniformStatement.{u} →
EisensteinUniformCuspidalExpansionOneStatement.{u}`,

with `EisensteinUniformCuspidalExpansionOneStatement` the one-function proposition of module
`AdelicEisensteinUniformCuspidalExpansionFamily`.

## The uniform convergent expansion

Provenance: derived. `ConvergentCuspidalTestExpansionUniformStatement` has the binders and the
conclusion of `ConvergentCuspidalTestExpansionStatement` (module
`AdelicConvergentCuspidalTestExpansionStatement`; Bernstein–Lapid, *On the meromorphic
continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), §6.10, (6.17), (6.18) and
(6.20), pp. 207–209, in the norm-one Levi tests (6.8) of §6.2, p. 202), with two changes:

1. **Uniform degree.** A natural number \(k\) is chosen together with the threshold and the
   competing labels, before the parameter. Each competing term satisfies
   `fam.HasPolynomialOrbit J (data.label j λ) k (terms j)`, the degree-\(k\) form of
   `fam.HasUnnormalizedExponent J (data.label j λ) (terms j)`.
2. **Absolute convergence.** For every Levi cusp form `test` on \(M_J\) and every \(g\), the
   integrands of the two tested constant terms on the left, that of
   \(C_JE(\varphi,\lambda)\) and that of \(C_{Q,J}\) of the selected intertwining integral
   `hK.intertwiningIntegral (fam.iU I) (fam.iU Q ≫ fam.p Q) n φ λ`, are integrable on the
   norm-one rational quotient of \(M_J\).

In (6.18) the summand of a Weyl element \(w\) is
\([M(w,\lambda)(C^{\mathrm{cusp}}_{P,P_w}\varphi)]_{w\lambda}\). Decompose the cuspidal constant
term \(C^{\mathrm{cusp}}_{P,P_w}\varphi\) into components with normalized exponents \(\mu\), each
with a bound on its polynomial degree. By (6.4) and (6.15), \(M(w,\lambda)\) carries a component of
normalized label \(\mu\) to a function of normalized label \(w\mu\), and the bound on the polynomial
degree is kept: in (6.14)–(6.15) the degree of the polynomial attached to an exponent is smaller
than the multiplicity of that exponent in the list. The target twist \([\cdot]_{w\lambda}\) then
supplies \(w\tilde\lambda\), where \(\tilde\lambda\) is the restriction of \(\lambda\) to the source
parabolic \(P_w\) of the piece. So the target-twisted image of a \(\mu\)-component has normalized
label \(w(\mu+\tilde\lambda)\), as in (6.19)–(6.21), and its polynomial degree is bounded by the
degree bound of the component. In the paper these bounds of the cuspidal components do not depend
on \(\lambda\), and their maximum bounds every competing summand of the projected expansion
(6.20)–(6.21).

The formal statement asks for one bound \(k\) for the competing terms of the scalar comparison,
and the proof of the uniform statement from its analytic inputs (module
`CuspidalTestExpansion.Reduction`) obtains it from other components. Its competing terms come from
the exponent components of the full constant terms \(C_{I_v}\varphi\), not of their cuspidal
projections. For each full-target Bruhat piece \(v\), `fullPiece_expansion` (module
`CuspidalTestExpansion.FullPiece`) gives a bound \(k_v\), independent of \(\lambda\): the
supremum of the degree bounds of the unnormalized exponent components of \(C_{I_v}\varphi\),
which the intertwining integral keeps. The witness \(k\) is `Finset.univ.sup kv`, the maximum of
the \(k_v\) over the full-target pieces, chosen before the parameter.

Formulas (6.20)–(6.21) are memberships of cuspidal projections, not identities of pairings. The
formal statement reads them through scalar tests: by (6.8), the pairing on the norm-one quotient
\(M_J(F)\backslash M_J(\mathbb A)^1\) with a cusp form does not change when a function is
replaced by its cuspidal projection. Here the test is a Levi cusp form on the full quotient
\(M_J(F)\backslash M_J(\mathbb A)\) (`fam.IsLeviCuspForm Kinf rho J test`), and the pairing
`fam.leviPairing J · g test` integrates over its norm-one quotient. Bernstein–Lapid define this
pairing when the integral converges absolutely. Item 2 requires the pairing integrands to be
integrable. The proof of the uniform statement obtains this from the polynomial growth bounds of
the functions that are paired and from the rapid decay of Levi cusp forms
(`LeviCuspFormRapidDecayStatement`).

## The proof

Apply the uniform statement with second index \(Q=I\), the Weyl representative \(1\) of
`normalizerPoints fam.i` and the identity Levi conjugation `𝟙 (fam.M I)`, which is a Weyl
conjugation by `isWeylConjugation_one` (module `AdelicSelfWeylParameters`). The image of \(1\) in
the relative Weyl group is \(1\) (`QuotientGroup.mk_one`), and `schemeWeylCharacterAction` is a
group homomorphism, so it acts trivially; hence both conditions on the simple roots of \(I\) hold.
The competing labels then have type `CompetingWeylExponents fam I J 1`.

The selected term is the intertwining integral of the representative \(1\) with the radical of
\(P_I\) as target. By `IsIwasawaCompact.intertwiningIntegral_one_self` (module
`AdelicIntertwiningIdentity`) it equals the twist \(\varphi_\lambda\) at every point, because
\(\varphi\) is left invariant under \(U_I(\mathbb A)\), which lies in \(U_I(\mathbb A)M_I(F)\). Rewriting
the selected term in the integrability and the identity gives the one-function proposition with
the same threshold, labels and degree bound. No hypothesis is added and the universe \(u\) is
kept.
