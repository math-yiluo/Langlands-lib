# Generic injectivity of Eisenstein series (proof)

Module `Langlands.Global.AdelicEisensteinGenericInjectivityProof` proves

`Langlands.Global.eisensteinGenericInjectivity : EisensteinGenericInjectivityStatement.{u}`,

the statement of the module `Langlands.Global.AdelicEisensteinGenericInjectivityStatement`
(Bernstein–Lapid, formula (8.4)); its page gives the statement and its correspondence with the
source. In words: for the data of that statement, finitely many automorphic forms
`φ_i ∈ 𝒜_P` and any functions `E_i` that are meromorphic in linear coordinates with a common
domain of holomorphy `D` and agree with the Eisenstein series `E(φ_i, λ)` for `Re λ`
sufficiently regular, every linear chart `e : ℂⁿ ≃ X^*(P) ⊗ ℂ` has an open dense set `O ⊆ ℂⁿ`
such that, for `s ∈ O` with `e s ∈ D`, a relation `∑_i c_i E_i(e s) = 0` forces
`∑_i c_i φ_i = 0`. The proof adds no hypothesis; it depends on the axioms `propext`,
`Classical.choice` and `Quot.sound` only.

The complete type, printed by `PrettyPrinter.ppSignature` (the `#check` form), with the
namespaces of the page of `Langlands.Global.EisensteinGenericInjectivity.PlaceHeight` open:

```lean
Langlands.Global.eisensteinGenericInjectivity.{u} : EisensteinGenericInjectivityStatement
```

## Proof

Fix the data of the statement and a chart `e : ℂⁿ ≃ X^*(P) ⊗ ℂ`.

1. **Trivial case.** If the index type is empty, `O = ℂⁿ`.
2. **Domain.** Otherwise the meromorphy hypothesis makes `D' = e⁻¹(D)` open and dense in `ℂⁿ`.
3. **Basis subfamily.** `Submodule.exists_fun_fin_finrank_span_eq` gives linearly independent
   `ψ_1, …, ψ_m` among the `φ_i`, `ψ_k = φ_{b k}`, spanning the same space, and coefficients with
   `φ_i = ∑_k co_{ik} ψ_k`.
4. **Common threshold.** Take `R` at least every threshold of the absolute convergence theorem
   `Langlands.Global.eisensteinAbsoluteConvergence` (module
   `Langlands.Global.AdelicEisensteinConvergenceProof`) for the `φ_i` and every agreement
   threshold of the hypothesis; regularity at a larger threshold implies regularity at a smaller
   one (`ParabolicRootPresentation.IsRegularParameter.mono`, module
   `Langlands.Global.AdelicRootHyperplaneReduction`). On the set `Reg` of `s` with `e s`
   `R`-regular, `E_i(e s)` is the absolutely convergent series `E(φ_i, e s)`. `Reg` is open
   (`isOpen_setOf_isRegularParameter`, module
   `Langlands.Global.AdelicEisensteinContinuationReduction`) and nonempty
   (`ParabolicRootPresentation.exists_regularParameter`, module
   `Langlands.Global.AdelicEisensteinRegularRegion`).
5. **Relations.** On `Reg` the series is linear in the section
   (`IsIwasawaCompact.eisensteinSeries_eq_finset_sum_of_twist`, module
   `Langlands.Global.AdelicEisensteinTwistComparison`, with the summability of step 4). Hence
   `E_i = ∑_k co_{ik} E_{b k}` on `Reg ∩ D'`. Both sides are meromorphic with domain `D'`
   (`IsMeromorphicOn.sum`, `IsMeromorphicOn.mul_const`), so the identity theorem
   `IsMeromorphicOn.eqOn_of_eqOn_open` (module `Langlands.Analysis.Meromorphic.ScalarIdentity`)
   extends it to `D'`.
6. **Anchor.** `exists_regular_det_ne_zero` (module
   `Langlands.Global.EisensteinGenericInjectivity.Anchor`), applied to the `ψ_k` and the
   nonempty open set `Reg ∩ D'`, gives `s₁ ∈ Reg ∩ D'` and points `g_i` with
   `det(E(ψ_k, e s₁)(g_i)) ≠ 0`.
7. **Generic set.** `det_E(s) = det(E_{b k}(e s)(g_i))` is meromorphic with domain `D'`
   (`isMeromorphicOn_det`, module `Langlands.Global.EisensteinGenericInjectivity.MeromorphicDet`)
   and equals the determinant of step 6 at `s₁`. Put `O = {s ∈ D' : det_E(s) ≠ 0}`. It is open
   because `det_E` is holomorphic on `D'`. It is dense: if an open `V` missed `O`, `det_E` would
   vanish on `V ∩ D'` and, by the identity theorem, on `D'`, contradicting step 6.
8. **Conclusion.** Let `s ∈ O` and `∑_i c_i E_i(e s) = 0`. By step 5 the vector
   `d_k = ∑_i c_i co_{ik}` satisfies `∑_k d_k E_{b k}(e s)(g) = 0` for all `g`, in particular at
   the `g_i`; since `det_E(s) ≠ 0`, `d = 0` (`Matrix.eq_zero_of_mulVec_eq_zero`). Hence
   `∑_i c_i φ_i = ∑_k d_k ψ_k = 0`.

The set `O` depends on the chart, on the given continuations and on the points of the anchor.
The proof uses of the continuations only that they are meromorphic with domain `D` and agree with
the series on regular parameters, and of the series only its absolute convergence.

The anchor rests on the modules `Langlands.Global.EisensteinGenericInjectivity.*`:
holomorphy of the convergent series along complex lines (`AnchorBasics`), extraction of one
coefficient of an absolutely convergent exponential series (`Cesaro`, `ProductTsum`), and the
separation of the heights of coset tuples along an archimedean ray of the split component
(`Separation`), which uses a Chevalley line for `P` with a strict weight gap (`LineData`),
invariant Hermitian energies at the infinite places (`Energy`, `PlaceHeight`), the ray
(`Ray`) and polynomials in the ray parameter (`Poly`).

## Sources

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
Math. Soc. 37 (2024):

- Remark at the end of §8.5, formula (8.4), printed p. 225: for `Q = P` and `w = e`, on any
  finite-dimensional linear subspace of `𝒜_P` the operator `φ ↦ E(φ, λ)` is injective for
  generic `λ ∈ X_P`.
- §8.5, printed pp. 224–225: Bernstein–Lapid deduce (8.4) from the constant term formula
  (6.17) of §6.10 (Geometric lemma, printed p. 208), a difference operator `D(λ)` built from a
  regular `a ∈ A_Q`, and the resultant `R(λ)`, an analytic function that is not identically
  zero.
- §2.2, printed p. 191: the Eisenstein series (2.1) and its absolute, locally uniform
  convergence for `Re λ` sufficiently regular; §2.3, Theorem (1), printed p. 191: its
  meromorphic continuation.
- §3.1, printed p. 192: meromorphic functions (holomorphic on an open dense set, with local
  holomorphic denominators), the notion behind `IsMeromorphicOn`.

The Lean proof does not follow the route of §8.5: it uses neither the constant term formula nor
intertwining operators, and works directly with the absolutely convergent series and the given
continuations.
