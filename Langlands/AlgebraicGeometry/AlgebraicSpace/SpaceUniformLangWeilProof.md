# Proof: Conrad's Lemma 4.6 for algebraic spaces

Author: Worker 5406 (Task 5995). The composition is the one recorded in the context of
Task 5202.

`Langlands.AlgebraicGeometry.AlgebraicSpace.spaceUniformLangWeil.{u}` proves the published
statement `Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceUniformLangWeilStatement.{u}` for an
arbitrary universe `u`. It imports the statement's Lean/Markdown pair unchanged and adds no
hypotheses. No Lang–Weil, Hasse–Weil, Weil-conjecture or Bertini input enters as a hypothesis,
axiom or structure field. The only axioms used are `propext`, `Classical.choice` and
`Quot.sound`.

## The statement

This is the algebraic-space form of Lemma 4.6 of Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (2011; source `conrad-2011-weil-grothendieck-adelic-points`). Conrad
needs it in the proof of Theorem 5.9 (printed p.17). Let `B` be a quasi-separated algebraic space
of finite type over `ℤ`. Let `f : Y ⟶ B` be a separated, quasi-compact, surjective morphism of
algebraic spaces with geometrically connected fibres. Assume `f` is smooth of relative
dimension `d` on an étale chart square. Then there is a real `C > 0` with the following
property. For every finite field `κ` and every `κ`-point `x` of `B`, let `N_x` be the number of
`κ`-points of `Y` over `x`. Then `|N_x − (#κ)^d| ≤ C (#κ)^(d − 1/2)`. The precise formulation
and its comparison with Conrad's text are in `SpaceUniformLangWeilStatement.md`.

## The proof

The proof is a term that composes four published theorems from namespace
`Langlands.AlgebraicGeometry.LangWeil`:

```lean
LangWeil.spaceUniformLangWeilOfFamily
  (LangWeil.familyLangWeilOfPlaneCurve LangWeil.planeCurveHasseWeil)
  LangWeil.familyPointUpperBound
```

1. `planeCurveHasseWeil : PlaneCurveHasseWeilStatement` is Schmidt's Hasse–Weil bound for
   absolutely irreducible plane curves over finite fields, proved by Stepanov's method
   (W. M. Schmidt, *Zur Methode von Stepanov*, 1973; source
   `schmidt-1973-zur-methode-von-stepanov`).
2. `familyLangWeilOfPlaneCurve : PlaneCurveHasseWeilStatement → FamilyLangWeilStatement` is the
   dimension induction. It handles fibre dimension 0 with `familyLangWeilZero` and fibre
   dimension 1 with the curve case `familyLangWeilCurve`. Higher dimensions follow by
   hyperplane slicing with `familyLangWeilSlicing`, using the Bertini theorem
   `BertiniGenericHyperplane.bertiniGenericHyperplaneStatement` and the upper bound
   `familyPointUpperBound` (Lang–Weil 1954, source `lang-weil-1954-number-of-points`; Tao 2012,
   source `tao-2012-lang-weil-bound`). Applied to step 1, it gives the uniform Lang–Weil
   estimate for geometrically irreducible families of schemes over `ℤ` in every fibre
   dimension.
3. `familyPointUpperBound : FamilyPointUpperBoundStatement` is the uniform upper bound for point
   counts in families (Lang–Weil 1954, Lemma 1; Tao 2012, Lemma 1).
4. `spaceUniformLangWeilOfFamily :
   FamilyLangWeilStatement → FamilyPointUpperBoundStatement → SpaceUniformLangWeilStatement`
   reduces algebraic spaces with étale charts to scheme families. It covers `B` by finitely many
   affine scheme charts through which every finite-field point of `B` factors, and it
   stratifies by schemes. The family estimate counts the top stratum, and the upper bound
   controls the lower strata (modules `SpaceUniformLangWeilOfFamilyProof` and `SpaceFamily/`).

Step 4 is applied to the output of step 2 and to step 3. This gives the statement with no
remaining hypothesis.

## Coverage note

The proof follows the elementary Lang–Weil route, not Deligne's Weil II, and uses no étale
cohomology, trace formula or weight argument. Lean names are in namespace
`Langlands.AlgebraicGeometry.LangWeil`, and modules are under
`Langlands/AlgebraicGeometry/LangWeil/`. The rows are exactly the theorems in this proof's
import closure on that route.

| Cited result | Library statement / theorem | Module of the proof |
|---|---|---|
| Schmidt 1973, Satz (printed p.347): Hasse–Weil bound for absolutely irreducible plane curves | `PlaneCurveHasseWeilStatement` / `planeCurveHasseWeil` | `PlaneCurveHasseWeilProof` (via `PlaneCurveHasseWeilReduction`) |
| Schmidt 1973, Section 2 (printed p.349): elementary coordinate reductions (derived; motivated by Section 2) | `PlaneCurveElementaryReductionsStatement` / `planeCurveElementaryReductions` | `PlaneCurveElementaryReductionsProof` |
| Schmidt 1973, Sections 5–6 (printed pp.355–359; Hilfssätze 5–6, equations (27)–(38)) and Sections 8–9 (printed pp.361–367; higher differentials for `q = p^κ`): Stepanov's auxiliary norm polynomials | `StepanovNormPolynomialsStatement` / `Stepanov.stepanovNormPolynomials` | `Stepanov/NormPolynomials` and the helper modules under `Stepanov/` |
| Schmidt 1973, Section 7 (printed pp.359–360, equation (40) and the parameter choice after it) and Section 9 (printed p.367): counting step after Hilfssatz 6 | `StepanovCountingStatement` / `stepanovCounting` | `StepanovCountingProof` |
| Lang–Weil 1954, Lemma 1 (printed p.820); Tao 2012, Lemma 1: uniform upper bound | `FamilyPointUpperBoundStatement` / `familyPointUpperBound` | `FamilyPointUpperBoundProof` (via `FiniteNormalizationCoverProof`, `NormalizationCoverPointBound`) |
| Tao 2012, Section 2: curve case through a plane model | `FamilyLangWeilCurveStatement` / `familyLangWeilCurve`; `FamilyCurvePlaneComparisonStatement` / `familyCurvePlaneComparison` | `FamilyLangWeilCurveProof`, `FamilyCurvePlaneComparisonProof` |
| Stacks Lemma 37.32.3 (Tag 0G4F): Bertini for the generic hyperplane section | `BertiniGenericHyperplaneStatement` / `BertiniGenericHyperplane.bertiniGenericHyperplaneStatement` | `BertiniGenericHyperplaneProof` |
| Lang–Weil 1954, proof of Theorem 1, induction step by hyperplane slicing (printed pp.822–823); Tao 2012, Section 2 | `FamilyLangWeilSlicingStatement` / `familyLangWeilSlicing` | `FamilyLangWeilSlicingProof` |
| Lang–Weil 1954, Theorem 1 with `r = 0` | `FamilyLangWeilZeroStatement` / `familyLangWeilZero` | `FamilyLangWeilZeroProof` |
| Lang–Weil 1954, Theorem 1; Tao 2012, Theorem 2, uniformly in families: the dimension induction | `FamilyLangWeilOfPlaneCurveStatement` / `familyLangWeilOfPlaneCurve` (conclusion `FamilyLangWeilStatement`) | `FamilyLangWeilOfPlaneCurveProof` |
| Conrad 2011, Lemma 4.6 for algebraic spaces, as used in the proof of Theorem 5.9 (printed p.17) | `SpaceUniformLangWeilOfFamilyStatement` / `spaceUniformLangWeilOfFamily` | `SpaceUniformLangWeilOfFamilyProof` and `SpaceFamily/` |

Sources: `schmidt-1973-zur-methode-von-stepanov`, `lang-weil-1954-number-of-points`,
`tao-2012-lang-weil-bound`, `stacks-bertini-theorems-0g4c-0fd4-2026-11-09` and
`conrad-2011-weil-grothendieck-adelic-points`. The page references are those of the
statements' Markdown files.

Two Schmidt rows need a qualification. Hilfssatz 3 (printed p.350) is proved only in a variant
form, as `Stepanov.frobeniusIndependence` in `Stepanov/FrobeniusIndependence`. Its hypothesis
`n·d + m(n−1)² < q` is Schmidt's inequality (16) on printed p.351, which his degree bound
implies. Hilfssätze 1–2 and 4 are not formalized as stated: resultants replace Schmidt's norms
and symmetric functions, and power-series branches (`Stepanov/Taylor`, `Stepanov/Branch`,
`Stepanov/PointBranch`) replace Hilfssatz 4.
