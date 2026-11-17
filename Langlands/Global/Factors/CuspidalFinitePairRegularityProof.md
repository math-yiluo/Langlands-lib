# Regularity of the finite pair L-factors of unitary cuspidal realizations on `Re(s) ≥ 1`

Authors: Worker 3657 (proof draft, Task 7358 shared drafts revisions 1–2) and
Worker 829 (merge into one module, verification, submission).

Lean module: `Langlands.Global.Factors.CuspidalFinitePairRegularityProof`. It
proves the published statement
`Langlands.Global.CuspidalFinitePairRegularityStatement` (module
`Langlands.Global.Factors.CuspidalFinitePairRegularityStatement`) for Task 7358
(`d1aad7bf-655e-4219-9022-9a2bdba3abe8`). It changes no published file.

## Main theorem

```lean
theorem Langlands.Global.cuspidalFinitePairRegularity :
    CuspidalFinitePairRegularityStatement.{u, uQ}
```

This is exactly the target, with both universes and no extra hypotheses. Take
unitary cuspidal realizations `T`, `T'` with spectral presentations `P`, `P'`
whose finite components are irreducible and admissible. Take finite pair
L-data `c`, a finite place `v`, and `s` with `1 ≤ Re s`. Then
`(c.lPolynomial v).eval (q_v^(-s)) ≠ 0`.

## Declarations

1. `cuspidalFinitePairRegularity_of_unitaryGeneric`: assuming the local p-adic
   statement `RankinSelberg.UnitaryGenericLPolynomialNonvanishingStatement.{u, u, u}`
   (Getz–Hahn Theorem 11.5.2, p-adic case), the target holds.
2. `cuspidalFinitePairRegularity`: the target. It applies (1) to the proof
   `RankinSelberg.UnitaryGeneric.unitaryGenericLPolynomialNonvanishing.{u, u, u}`
   of that local statement. The proof is imported from module
   `Langlands.Representation.RankinSelberg.UnitaryGenericLPolynomialNonvanishingProof`,
   the proof of Task 6387 (`9dcb3206-7035-4d1c-9cea-f620e42f9628`).

The local statement is used with all three universes equal to `u`, because the
local components of a realization over `F : Type u` are carried in `Type u`.

## Proof of the reduction

Fix the data of the target. Write `A`, `A'` for the p-adic objects of the local
components of `P`, `P'` at `v` (`LocalRealization.padicObject`, built from the
irreducibility and admissibility `h v`, `h' v`).

1. **Unfolding the specification.** `c.lPolynomial_spec v` says that
   `c.lPolynomial v` is the automorphic pair L-polynomial of the classes of `A`
   and `A'`. The published `Correspondence.isAutomorphicPairLPolynomial_iff`,
   used with the identity equivalences `Representation.Equiv.refl`, turns this
   into `RankinSelberg.IsLanglandsPairLPolynomial` for `A.obj`, `A'.obj`:
   - Langlands data `d`, `e` (`TemperedLanglandsDatum`) exist with `A.obj`,
     `A'.obj` as their Langlands quotients;
   - for all such data, `c.lPolynomial v` is a symmetric JPSS L-polynomial
     (`IsPadicSymmetricLPolynomial`) of the standard modules
     `d.standardModule`, `e.standardModule`.
2. **Genericity and unitarity.** The proved
   `Automorphic.cuspidalUnitaryLocalGenericity` shows that `A.obj` and `A'.obj`
   are generic for the additive character `c.additive v` of the finite data.
   The proved `Automorphic.cuspidalUnitaryLocalUnitarity` shows that they are
   unitarizable.
3. **From standard modules to the components.** Let `ν` be the self-dual Haar
   measure `⟨c.measure v, c.measure_spec v⟩`. The proved
   `RankinSelberg.genericLanglandsQuotientLFactor` (JPSS (9.4)(4)), applied to
   `d`, `e` and the generic quotients, gives one polynomial `P₀`. It is a
   symmetric L-polynomial both of the standard modules and of `A.obj`, `A'.obj`.
   Uniqueness (`IsPadicSymmetricLPolynomial.unique`) for the standard modules
   gives `c.lPolynomial v = P₀`.
4. **The local statement.** The hypothesis, applied to the prime under `v`, the
   completion `padicField v`, `c.additive v`, `ν`, the representations `A.obj`,
   `A'.obj` with their genericity and unitarizability, the polynomial `P₀` and
   `s`, gives `P₀(q_v^(-s)) ≠ 0`.

## Provenance and route

- The target is the non-Archimedean case of Getz–Hahn (2024), *An Introduction
  to Automorphic Representations*, Theorem 11.5.2, printed p.305 (PDF 316),
  registered as `getz-hahn-2024-automorphic-representations`. It is applied to
  the local components of cuspidal representations as in the paragraph before
  Theorem 11.7.1, printed p.309 (PDF 320). In GH, `L(s, π × π') = P(q^(-s))⁻¹`
  (display (11.21), p.305); the target is the nonvanishing of `P` on
  `Re(s) ≥ 1`. The pair data `c` define the polynomial through standard modules
  of Langlands data, not through Whittaker models.
- The proof follows the route of the task and of the statement's Markdown:
  steps 1–4 above, then GH's deduction of Theorem 11.5.2 from Proposition 11.5.1
  in the local proof of Task 6387. That proof's own Markdown gives its route and
  sources.
- Step 3 is JPSS, *Rankin-Selberg convolutions* (1983), Proposition (9.4),
  display (4), printed p.458, registered as `jpss-1983-rankin-selberg`: the
  L-factor of a generic pair equals that of its standard modules. It is already
  proved in the Library.

## What is not asserted

Nothing about the Archimedean places, and nothing about the existence of the
finite pair data `c`.

## Lean checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (lake build,
inspecting `Langlands.Global.cuspidalFinitePairRegularity`) reports no errors or
warnings. The theorem depends only on `propext`, `Classical.choice` and
`Quot.sound`.
