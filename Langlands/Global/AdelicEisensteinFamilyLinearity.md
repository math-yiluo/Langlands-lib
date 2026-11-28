# Finite linear combinations in the cuspidal tests of convergent Eisenstein series

Module `Langlands.Global.AdelicEisensteinFamilyLinearity`. It collects elementary facts used to
pass from one inducing function to a finite family \(\sum_i a_i\varphi_i\) in the cuspidal tests
of Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc.
37 (2024), §6.10 (Corollary 6.10 and the norm-one tests (6.8) of §6.2). Provenance: internal;
every result is a direct consequence of the Library definitions named below.

All declarations are in namespace `Langlands.Global.StandardParabolicFamily` unless noted, for a
compatible standard family `fam` of a group `G` over a number field `F`.

## Polynomial orbits

`fam.HasPolynomialOrbit J λ k φ` (module `AdelicExponentPolynomials`) says that for every
\(g\) the function \(x\mapsto\varphi(xg)\,x^{-\lambda}\) on the positive split component
\(\mathfrak A_J\) is a polynomial of degree at most \(k\) in \(H_J(x)\).

- `hasPolynomialOrbit_of_degree_le`: if \(k\le k'\), a polynomial orbit of degree at most \(k\)
  has degree at most \(k'\). The degree-\(k\) polynomial functions span a subspace of the
  degree-\(k'\) ones (`Submodule.span_mono`).
- `hasPolynomialOrbit_const_mul`: \(x\mapsto c\,\varphi(x)\) has the same exponent and degree
  bound, with the polynomial \(c\,p\).

## Linearity of the norm-one Levi pairing

For a finite set \(s\), coefficients \(a_i\) and functions \(f_i\) on \(G(\mathbb A)\):

- `leviPairingIntegrand_finset_sum`: the integrand of `fam.leviPairing J` for
  \(\sum_{i\in s}a_if_i\) is \(\sum_{i\in s}a_i\) times the integrands of the \(f_i\).
- `integrable_leviPairingIntegrand_finset_sum` and `leviPairing_finsetSum`: if each integrand
  of \(f_i\) is integrable on the norm-one rational quotient of \(M_J\), so is that of the
  combination, and \(\langle\sum_ia_if_i,\psi\rangle_g=\sum_ia_i\langle f_i,\psi\rangle_g\)
  (`integral_finsetSum`, `integral_const_mul`).
- `leviPairingIntegrand_const_mul` and `leviPairing_const_mul`: the same for one term, with no
  integrability hypothesis.

## Linearity of constant terms

- `integrable_constantTermIntegrand_of_rationalInvariant`: if \(f\) is continuous and left
  invariant under \(G(F)\), then for every \(g\) the integrand \(u\mapsto f(ug)\) of
  `fam.constantTerm J` on \(U_J(F)\backslash U_J(\mathbb A)\), at the chosen representatives, is
  integrable. As in the Library's `integrable_constantTermIntegrand_of_le` (module
  `AdelicStandardConstantTerm`), the integrand descends to a continuous function on the compact
  quotient (`compactSpace_rationalQuotient_range_unipotent`), whose normalized measure is a
  probability measure. The invariance used is that under the rational points of \(U_J\),
  which lie in \(G(F)\) (`rationalImage_le_rationalSubgroup`).
- `constantTerm_finset_sum`: if every \(f_i\) has integrable constant-term integrands along
  \(J\), then \(C_J(\sum_ia_if_i)=\sum_ia_iC_Jf_i\) pointwise.
- `parabolicConstantTerm_finset_sum`: the same for `fam.parabolicConstantTerm P J`, assuming
  the integrability only when \(J\le P\); otherwise both sides are \(0\).

## Continuity and invariance of convergent series and twists

Here \(K\) is a compact with `hK : IsIwasawaCompact (fam.p I) K`.

- `isLeftInvariantUnder_parameterTwist`: if \(\varphi\) is left invariant under
  \(U_I(\mathbb A)M_I(F)\) (`parabolicQuotientSubgroup`), so is the twist
  \(\varphi_\lambda=\) `hK.parameterTwist φ λ`. The factor \(m_{P_I}(g)^\lambda\) is invariant
  under \(U_I(\mathbb A)\) (`heightPower_unipotent_mul`) and under \(M_I(F)\subset P_I(F)\)
  (`heightPower_rational_mul`, with `map_comp_apply_of_hom` and `map_rational_eq_rational`),
  hence under the group they generate (`isLeftInvariantUnder_sup`).
- `integrable_constantTermIntegrand_parameterTwist`: for \(J\le I\) and \(\varphi\) continuous and
  invariant under \(U_I(\mathbb A)M_I(F)\), the constant-term integrand of \(\varphi_\lambda\) along
  \(J\) is integrable, by `integrable_constantTermIntegrand_of_le`.
- `continuous_eisensteinSeries_of_compactBound`: if \(\varphi\) is continuous and on every compact
  set the terms \(\varphi_\lambda(\gamma g)\) of `hK.eisensteinSeries φ λ` are bounded by a
  summable sequence independent of \(g\), the series is continuous. Each term is continuous;
  on a compact neighbourhood of a point the sum is continuous by `continuousOn_tsum`, and
  \(G(\mathbb A)\) is locally compact. The bound is the one supplied by
  `EisensteinAbsoluteConvergenceStatement` for a sufficiently regular \(\lambda\).

## Concatenating competing Weyl labels

In namespace `Langlands.Global`:

- `CompetingWeylExponents.sigma`: for finitely many `data i : CompetingWeylExponents fam I J w`,
  \(i<m\), the family of all their labels, of size \(\sum_i\) `(data i).size`. The label with
  index \(k\) is the label with index \(j\) of `data i`, where \((i,j)\) is the image of \(k\) under
  the inverse of `finSigmaFinEquiv`; the Weyl element, linear part, offset and the three
  conditions are those of that label.
- `CompetingWeylExponents.sigma_label_index`: the corresponding equality of labels, which holds by
  definition.
