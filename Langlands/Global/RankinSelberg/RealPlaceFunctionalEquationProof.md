# Proof: the archimedean Rankin–Selberg functional equation at the real places

Module `Langlands.Global.RankinSelberg.RealPlaceFunctionalEquationProof`. The theorem

```lean
theorem Langlands.Global.RankinSelbergGlobal.realPlaceFunctionalEquation :
    RealPlaceFunctionalEquationStatement.{u}
```

proves `Langlands.Global.RankinSelbergGlobal.RealPlaceFunctionalEquationStatement` (module
`Langlands.Global.RankinSelberg.ArchimedeanFunctionalEquationStatement`) at an arbitrary
universe `u` of the number field, with no hypotheses.

## The statement

`RealPlaceFunctionalEquationStatement.{u}` is the conjunction
`RealUnequalFunctionalEquationStatement.{u} ∧ RealEqualFunctionalEquationStatement.{u}`; the
paired Markdown of `ArchimedeanFunctionalEquationStatement` gives the exact conventions. In
words (Jacquet 2009, Theorem 2.1 (i)–(iii), for `GL_n(ℝ) × GL_m(ℝ)`): let `F` be a number field
with `AdeleQuotient F` compact, `ψ` a unitary additive character of the adeles trivial on `F`,
and `T`, `Td`, `T'`, `Td'` actual cuspidal realizations with `Td`, `Td'` contragredient to `T`,
`T'`. Fix a real place `v`, the component `a` of `ψ` there (`IsRealAdditiveComponent ψ v a`),
and parameters `d`, `d'`, `dd`, `dd'` (`HasRealPlaceParameter`) of the four realizations at
`v`. For every quotient measure `D : RealQuotientMeasureData`, every pair `W`, `W'` of
archimedean restrictions at `v` of global Whittaker functions of `T` for `ψ` and of `T'` for
`ψ⁻¹` (`IsRealPlaceWhittaker`) and, in equal ranks, every Schwartz function `Φ`, there are
`σ : ℝ` and `M, Md : ℂ → ℂ` such that

1. the integrands of the local integral and of its dual integral are integrable for
   `σ < Re s` (for `D.measure`; in unequal ranks the dual kernel for the product of
   `D.measure` and the rectangular measure self-dual for `ψ_v`, `realUnequalDualMeasure`);
2. both integrals are holomorphic on `{σ < Re s}`;
3. `M`, `Md` are meromorphic on `ℂ` and equal the two integrals on `{σ < Re s}`;
4. off a discrete set (`Filter.codiscrete ℂ`),
   `L(s) Md(1 − s) = ω'(−1)^r ε(s) L∨(1 − s) M(s)`, where `L`, `L∨` are the inverses of the
   denominators of `realPairLFactor d d'` and `realPairLFactor dd dd'`,
   `ε = realPairEpsilon d d' a |a|^(1/2)` and `ω'(−1) = realMinusOneScalar T' v`.

The dual integral is `Ψ_(n−m−1)(s; ρ(w_(n,m)) W̃, W̃')` for `t < r` and `Ψ(s; W̃, W̃', Φ̂)`
with `Φ̂ = realFourierTransform a Φ` in equal ranks (including `r = 0`).

## Proof as implemented

The proof is a single term: the Library theorem `realPlaceUniformContinuationReduction` applied
to three proved theorems. All four are in the namespace `Langlands.Global.RankinSelbergGlobal`.

1. `realPlaceUniformContinuationReduction` (module `RealUniformContinuationReduction`) proves
   `RealPlaceUniformContinuationReductionStatement.{u}`, the implication

   ```lean
   RealLocalUniformUnequalContinuationStatement →
     RealLocalUniformPositiveEqualContinuationStatement →
     RealPlaceContragredientPairLStatement.{u} → RealPlaceFunctionalEquationStatement.{u}
   ```

   It adds the convergence and holomorphy conjuncts (proved for the uniform real Whittaker
   models `realUniformWhittakerModel` by `realUnequalPairConvergence` and
   `realEqualPairConvergence`) to the two continuation premises, and then applies
   `realPlaceUniformLocalTheoryReduction` (module `RealUniformLocalTheoryReduction`). That
   reduction shows that the actual archimedean restrictions lie in the uniform models
   (`realPlaceUniformWhittakerModel`), rewrites the dual denominators with the contragredient
   premise and the signs with the comparison of `realMinusOneScalar` with the parameter, and
   treats the equal-rank case `r = 0` by the real Tate argument.
2. `realLocalUniformUnequalContinuation : RealLocalUniformUnequalContinuationStatement`
   (module `RealLocalUniformUnequalContinuationProof`): the meromorphic continuation of the real
   unequal-rank integrals and their local functional equation, for functions in the uniform
   real Whittaker models of arbitrary real block lists.
3. `realLocalUniformPositiveEqualContinuation : RealLocalUniformPositiveEqualContinuationStatement`
   (module `RealLocalUniformPositiveEqualContinuationProof`): the same for the real equal-rank
   integrals at every positive rank index.
4. `realPlaceContragredientPairL : RealPlaceContragredientPairLStatement.{u}` (module
   `RealPlaceContragredientPairLProof`): the pair `L`-factor of the parameters `dd`, `dd'` of
   the contragredient realizations has the same denominator as that of the dualized blocks
   `d.map RealLocalJacquet.dualBlock`, `d'.map RealLocalJacquet.dualBlock`.

The universe parameter `u` is passed explicitly to the reduction and to the contragredient
theorem; the two continuation statements do not involve a number field and carry no universe.

## Declarations

- `realPlaceFunctionalEquation : RealPlaceFunctionalEquationStatement.{u}` (theorem).

## Relation to the literature

H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009), pp. 3–6: the integrals (2.4)–(2.6)
and Theorem 2.1; J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004),
Theorems 3.5–3.6, printed pp. 216–217. The statement keeps parts (i) and (iii) of Jacquet's
theorem and, of part (ii), the meromorphic continuation of both integrals; it does not contain
the assertion that the integrals are holomorphic multiples of the `L`-factor bounded in
vertical strips. The proof route is the Library's: a reduction of the actual archimedean
restrictions to uniform local Whittaker models and the local continuation theorems proved on
them, rather than Jacquet's text verbatim.
