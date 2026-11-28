# Schur formal degree under exact quotient Haar transport

`Langlands.Plancherel.representationFormalDegree_pullback` proves
`RepresentationFormalDegreePullbackStatement` with the three universes of the
statement kept independent. Write \(\sigma=\rho\circ e\) for the pullback and
\(d(\rho)\), \(d(\sigma)\) for the two values of `representationFormalDegree`.

The proof takes, from the square-integrability witnesses, the central
characters that `representationFormalDegree` itself chooses, and the scalar
actions of \(A\) on \(\rho\) and of \(B\) on \(\sigma\) that they give. It then
applies the uniqueness theorem `formalDegree_unique` for \(\rho\), \(A\) and the
quotient Haar \(\mu_G\). The first characterization it needs is
`orthogonalityIntegral_eq_representationFormalDegree` for \(\rho\). The second
asserts that for all \(v_1,v_2\in V\) and smooth dual vectors
\(\ell_1,\ell_2\) of \(\rho\) the orthogonality integral on \(G/A\) equals
\(d(\sigma)^{-1}\,\ell_2(v_1)\,\ell_1(v_2)\). It is proved as follows.

- By `isSmoothVector_dual_comp_continuousMulEquiv_iff`, the same linear
  functionals \(\ell_1,\ell_2\) are smooth dual vectors of \(\sigma\).
- The Schur integrand of \(\sigma\) on \(H/B\) equals the Schur integrand of
  \(\rho\) on \(G/A\) composed with the quotient isomorphism
  `quotientContinuousMulEquiv e A B hAB`. On a representative \(h\in H\) this
  is `quotientContinuousMulEquiv_mk` and `orthogonalityIntegrand_mk` on both
  sides, with \(e(h^{-1})=e(h)^{-1}\) for the second coefficient factor.
- Rewriting \(\mu_G\) as the pushforward of \(\mu_H\) by the hypothesis on the
  measures, `integral_map_equiv` for the measurable equivalence underlying the
  quotient homeomorphism identifies the orthogonality integral of \(\rho\) on
  \(G/A\) with that of \(\sigma\) on \(H/B\).
- `orthogonalityIntegral_eq_representationFormalDegree` for \(\sigma\), \(B\)
  and \(\mu_H\) evaluates the latter as
  \(d(\sigma)^{-1}\,\ell_2(v_1)\,\ell_1(v_2)\); the crossed evaluations are
  those of the same vectors and functionals.

Uniqueness then gives \(d(\rho)=d(\sigma)\). This is the invariance of the
characterization in Waldspurger III.1(3) under the group isomorphism and the
exact transport of the quotient Haar measure.

[Waldspurger (2003), III.1(3), printed p. 265](https://doi.org/10.1017/S1474748003000082)
