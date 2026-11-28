# Radical averages of adelic test functions on the Levi

`Langlands.Global.leviRadicalAverageTestFunction` proves
`Langlands.Global.LeviRadicalAverageTestFunctionStatement.{u}`. For the Levi map
`j = fam.l J ≫ fam.p J` and the closed adelic radical `N`, it shows that
\(m\mapsto\int_N \beta(u\,j(m))\,du\) is an adelic test function on the Levi,
using the normalized Haar measure specified in the statement.

## Parabolic structure and compact support

The split-component cocharacter \(\chi\) identifies the parabolic, the Levi,
and the radical with the dynamic subgroups \(P(\chi)\), \(Z(\chi)\), and
\(U(\chi)\). The inclusion of \(Z(\chi)\) in the normalizer of \(U(\chi)\)
gives the conjugation action of the adelic Levi on `N`.
`isClosedEmbedding_map_parabolic` gives the closed image of the adelic
parabolic. On that image, `leviProjection` is a continuous group homomorphism
that sends \(u\) to \(1\) and \(j(m)\) to \(m\), by
`leviProjection_leviMul`. The preimage of `tsupport β` in the parabolic image
is compact. Its image under `leviProjection` is a compact set outside which
\(\beta(u\,j(m))=0\) for every \(u\in N\). This bounds the support of the
average.

## Continuity and archimedean smoothness

For a compact set \(C\) of Levi points, `radicalSupport` is the preimage in
`N` of the image of \(\operatorname{tsupport}(\beta)\times C\) under
\((g,m)\mapsto g\,j(m)^{-1}\). This is compact by closedness of `N`, and the
integrand vanishes outside it for every \(m\in C\). Taking \(C\) to be a
compact neighbourhood of a Levi point reduces continuity there to
`continuous_parametric_integral_of_continuous` on a fixed compact set.

Fix a finite Levi point \(b\) and take \(C=C_\infty\times\{b\}\) via the
adelic product equivalence, with \(C_\infty\) a compact neighbourhood of an
archimedean Levi point. Write \(S\) for the resulting compact set in `N`.
On \(S\), the finite component \(u_f j_f(b)\) has finite image in the discrete
space \(G(\mathbb A_f)/L\), where \(L\) is an open right-invariance subgroup of
\(\beta\). For a coset \(q\) in this image, its indicator gives a continuous
weight on \(S\). Right invariance identifies the integrand on that coset
with the archimedean slice of \(\beta\) at a representative of \(q\), evaluated
at \(u_\infty j_\infty(m_\infty)\).

The archimedean Levi map is smooth by the coordinate criterion for
`ContMDiff`, and multiplication is smooth for the ambient Lie group.
`CompactManifoldVectorIntegral.contMDiff_weightedIntegral` gives smoothness
for the integral of each of these slices with its coset weight. The Haar
measure pulled back to \(S\) is finite. Linearity identifies the finite sum
of the weighted integrals with the original slice on \(C_\infty\), which gives
smoothness at the chosen point.

## Finite-place invariance and normalization

Right invariance follows by pulling back \(L\) along the finite Levi map.
For left invariance, pull back the intersection of the left-invariance
subgroup of \(\beta\) with a compact open subgroup \(W\) of \(G(\mathbb A_f)\).
If \(\ell\) belongs to this pullback, conjugation by \(j(\ell)\) preserves
the part of `N` cut out by \(W\) and a compact identity neighbourhood at
infinity. In the adelic product, this conjugation is trivial at infinity,
and the image of \(\ell\) at the finite places belongs to \(W\).
The preserved compact identity neighbourhood has finite positive Haar mass,
so the character by which the conjugation scales Haar measure is \(1\).
Changing variables by \(u\mapsto j(\ell)^{-1}u\,j(\ell)\) and using left
invariance of \(\beta\) gives left invariance of the average.

These arguments first use `Measure.haar` on `N`.
`AdelicSubgroupPoints.normalizedHaarMeasure` multiplies this measure by
`quotientMassNormalizer`. By `integral_smul_measure` the normalized average
is the corresponding scalar multiple of the average for `Measure.haar`.
Multiplying by a constant preserves the test-function conditions.

## Provenance

Mœglin and Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
I.1.13, use the normalized \(U(\mathbb A)\)-integral as the inner integral of
the standard-parabolic Iwasawa formula. The theorem gives the test-function
regularity of that average upon restriction to the Levi. The related
smoothness assertion in I.2.6 concerns constant terms integrated over
\(U(F)\backslash U(\mathbb A)\). The Lean argument proves the derived
regularity result using the compact-support and finite-coset arguments above.

- `moeglin-waldspurger-1995-spectral-decomposition`,
  `05.1_pp_1_18_Hypotheses_and_general_notation.pdf`, I.1.13, printed and
  PDF p. 18. SHA-256 `f629f59c8774b80b155f60ef935ceccd4c5c5c1e87a1ea793baec0875749e770`.
  [I.1, Hypotheses and general notation](https://doi.org/10.1017/CBO9780511470905.003)
- `moeglin-waldspurger-1995-growth-and-constant-terms`,
  `05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`, I.2.6, printed
  p. 27, PDF p. 10. SHA-256 `296dcb3e7170bb0c2689cf0c79136a43cd86976df2b4c51f027cf9365f7fe988`.
  [I.2, Automorphic forms](https://doi.org/10.1017/CBO9780511470905.004)
