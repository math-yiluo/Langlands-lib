# The finite-place layer of the cuspidal pair functional equation

Author: Worker 4891.

This module proves the local and finite-place parts of the completed global
Rankin–Selberg functional equation for cuspidal pairs, in the formulation of
`CuspidalPairFactorData.lean` and `CuspidalPairFunctionalEquationStatement.lean`.
Let `F` be a number field, `ψ` a unitary additive character of the adeles trivial on
`F`, and `P`, `P'`, `Pd`, `Pd'` spectral presentations of cuspidal realizations of
`GL_(r+1)` and `GL_(t+1)` whose finite components are irreducible and admissible.
The theorems give:

1. a finite factor choice `FinitePairFactorChoice ψ P P' Pd Pd' h h' hd hd'`;
2. an additive component of `ψ` at every real and every complex place;
3. one finite set `S` of finite places that contains the four exceptional sets and
   satisfies `FiniteAdditiveSupport ψ S`, such that every finite factor choice is
   unramified outside `S` (`IsUnramifiedOutside S`).

These are the four conjuncts of `CuspidalPairLocalDataStatement`. The theorem
`cuspidalPairLocalData` in `CuspidalPairLocalDataProof.lean` assembles them. The
mathematics is Cogdell 2004, Theorem 3.3 (printed page 215), and Getz–Hahn 2024,
Section 11.6 (printed page 308): at almost all places the representations and `ψ`
are unramified, the local L-factor is the Euler factor of the Satake parameters, and
the epsilon factor is `1`.

## Local existence and the unramified places

- `exists_isAutomorphicPairLPolynomial`, `exists_isAutomorphicPairEpsilonFactor`:
  for a `p`-adic field `K`, a nontrivial additive character and a self-dual
  measure, every pair of classes `(π, π')` has a pair L-polynomial and a pair
  epsilon factor. A class has a representative. The published
  `RankinSelberg.langlandsPairLFactorExistence` and
  `langlandsPairEpsilonFactorExistence` give the factor of the representatives, and
  `isAutomorphicPairLPolynomial_iff` and `isAutomorphicPairEpsilonFactor_iff`
  transfer it to the classes.
- `pairEulerPolynomial_ofTuple`: the pair Euler polynomial of two enumerated spectra
  is `∏ i, ∏ j, (1 - z_i z'_j X)`, by `Multiset.prod_map_product_eq_prod_prod`.
- `isAutomorphicPairLPolynomial_eq_pairEulerPolynomial`: if the objects `A` and `A'`
  have spherical spectra `s` and `s'`, every pair L-polynomial of their classes,
  for a self-dual measure, is `pairEulerPolynomial s s'`. This is
  `Correspondence.unramifiedDatum_lPolynomial_eq` (module `UnramifiedPairFactors`)
  applied to the data from `exists_unramifiedDatum_isLanglandsQuotient`.
- `isAutomorphicPairEpsilonFactor_eq_one`: under the same hypotheses, and if `ψ` has
  additive conductor zero, every pair epsilon factor is `(1, 0)`, by
  `Correspondence.unramifiedDatum_epsilonFactor_eq`.

## Additive components

- `canonicalFiniteAdditiveComponent ψ hdiag v` is the restriction of `ψ` to the
  completion at the finite place `v`, a nontrivial character continuous for the
  canonical topology of `padicField v`. The topology is transported by
  `completion_topology_eq`, and the character is nontrivial by the published
  `finiteAdditiveRestriction_ne_one`. It satisfies
  `IsCanonicalFiniteAdditiveComponent` by definition.
- `additiveConductor_congr`: two characters with the same underlying additive
  character, for equal topological data, have the same additive conductor.
- `exists_finiteAdditiveSupport`: there is a finite set `S0` with
  `FiniteAdditiveSupport ψ S0`. The published `adelicDuality` gives the adelic
  self-duality pairing. From it, the published
  `exists_finset_additiveConductor_eq_zero_of_pairing` gives a finite set outside
  which the restrictions of `ψ` have conductor zero for the completion topology.
  Since `topologicalData_eq_canonicalTopologicalData`, the canonical components
  have the same conductors (`additiveConductor_congr`).
- `finiteAdditiveSupport_mono`: `FiniteAdditiveSupport` passes to larger sets.
- `exists_isRealAdditiveComponent`, `exists_isComplexAdditiveComponent`: the
  published `isRealAdditiveComponent_realCompletionAdditiveScale` and its complex
  analogue, with `infiniteAdditiveRestriction_ne_one`.

## Global statements

- `nonempty_finitePairFactorChoice`: at every finite place take the canonical
  component of `ψ`, the published self-dual measure `localSelfDualHaar`, and chosen
  factors from the two local existence theorems.
- `hasSphericalSpectrum_padicObject`: at `v ∉ P.exceptional`, the canonical `p`-adic
  object of the local component has spherical spectrum
  `P.spectralSystem.eigenvalues v hv`. The presentation gives the Hecke-eigenvalue
  form (`P.hasSpectrum`). It reaches the class through
  `hasSphericalHeckeSpectrumClass_iff` and `hasSphericalHeckeSpectrumClass_classOf`,
  and the published `sphericalHeckeComparison` converts it to the
  principal-series form.
- `exists_isUnramifiedOutside`: take `S = S0 ∪ P.exceptional ∪ P'.exceptional ∪
  Pd.exceptional ∪ Pd'.exceptional`. Let `c` be any factor choice and `v ∉ S`. Both
  L-polynomials are pair Euler polynomials by
  `isAutomorphicPairLPolynomial_eq_pairEulerPolynomial`, since `c.measure v` is
  self-dual for `c.additive v`. The additive component `c.additive v` and the
  conductor-zero witness of `FiniteAdditiveSupport` are both canonical components
  of `ψ`, so they have the same underlying character, and `c.additive v` has
  conductor zero. Then `c.epsilon v = (1, 0)` by
  `isAutomorphicPairEpsilonFactor_eq_one`.

The theorems use only that `ψ` is trivial on `F`. The nontriviality hypothesis on `ψ`
and the contragredient hypotheses of the target are not used. The universes `u` and
`uQ` are arbitrary.

## References

- J. W. Cogdell, *Analytic theory of L-functions for `GL_n`*, in J. Bernstein and
  S. Gelbart (eds.), *An Introduction to the Langlands Program*, Birkhäuser, 2004,
  197-228 (`cogdell-2004-analytic-theory-gln`), Theorem 3.3, printed page 215.
- J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations* (2024)
  (`getz-hahn-2024-automorphic-representations`), Section 11.6, printed page 308.
