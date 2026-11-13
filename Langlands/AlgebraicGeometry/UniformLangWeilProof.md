# Proof of Conrad's Lemma 4.6 for schemes

Author: Worker 7. The composition was proposed by Worker 5202 in the context of Task 5993.

This module proves the published statement
`Langlands.AlgebraicGeometry.UniformLangWeilStatement` with the theorem
`Langlands.AlgebraicGeometry.uniformLangWeil`, in an arbitrary universe `u`. It imports the
statement's Lean/Markdown pair unchanged. It adds no hypotheses and introduces no axiom or
structure field. The proof uses only Lean's standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## The statement

The statement is Lemma 4.6 of Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(2011), printed p.12, for schemes (registered source
`conrad-2011-weil-grothendieck-adelic-points`). Let `B` be a quasi-compact scheme that is locally
of finite type over `Spec ℤ`. Let `f : Y ⟶ B` be smooth, separated, surjective, locally of finite
type, quasi-compact and geometrically connected, with every fibre of pure dimension `d`. Then
there is a real `C > 0` with the following property. Let `b` be a closed point of `B`, let `q_b`
be the number of elements of its residue field, and let `N_b` be the number of rational points
of the fibre over `b`. Then `|N_b − q_b^d| ≤ C q_b^(d − 1/2)`.

Conrad's own proof uses Deligne's Weil II. This proof does not.

## The proof

The proof is one term, the composition of three published Library theorems in namespace
`Langlands.AlgebraicGeometry.LangWeil`:

```lean
theorem uniformLangWeil : UniformLangWeilStatement.{u} :=
  LangWeil.uniformLangWeilOfFamily
    (LangWeil.familyLangWeilOfPlaneCurve LangWeil.planeCurveHasseWeil)
```

1. `planeCurveHasseWeil : PlaneCurveHasseWeilStatement.{u}`
   (module `Langlands.AlgebraicGeometry.LangWeil.PlaneCurveHasseWeilProof`). This is Schmidt's
   bound for absolutely irreducible plane curves over finite fields, proved by Stepanov's method
   (W. M. Schmidt, *Zur Methode von Stepanov*, 1973, Satz on printed p.347; registered source
   `schmidt-1973-zur-methode-von-stepanov`).
2. `familyLangWeilOfPlaneCurve : PlaneCurveHasseWeilStatement.{u} → FamilyLangWeilStatement.{u}`
   (module `Langlands.AlgebraicGeometry.LangWeil.FamilyLangWeilOfPlaneCurveProof`). This is the
   dimension induction. Fibre dimension `0` is the zero case `familyLangWeilZero`. Dimension `1`
   is the curve case `familyLangWeilCurve`, which uses the plane-curve bound and the uniform
   upper bound `familyPointUpperBound`. Dimension `n + 1` gives dimension `n + 2` by hyperplane
   slicing (`familyLangWeilSlicing`), which uses the generic Bertini theorem and the same upper
   bound. The conclusion `FamilyLangWeilStatement` is the uniform Lang–Weil estimate for families
   with geometrically irreducible fibres of pure dimension `d`, over a base of finite type over
   `ℤ`. It holds at every `κ`-point of the base, for every finite field `κ`, with one constant.
3. `uniformLangWeilOfFamily : FamilyLangWeilStatement.{u} → UniformLangWeilStatement.{u}`
   (module `Langlands.AlgebraicGeometry.LangWeil.UniformLangWeilOfFamilyProof`). This is the
   reduction from Conrad's smooth, geometrically connected families to geometrically irreducible
   ones. A smooth, geometrically connected morphism is geometrically irreducible. The residue
   field of a closed point of `B` is finite. The rational points of the fibre over `b` are in
   bijection with the lifts of `Spec κ(b) ⟶ B` to `Y`. The family estimate at `κ = κ(b)` is then
   exactly the inequality of the target, with the same constant. Separatedness and
   surjectivity of `f` are not used.

The module imports only the three proof modules above. Their import closures contain all the
modules in the table below.

## Coverage note

The proof uses the elementary Lang–Weil route: Schmidt's plane-curve bound by Stepanov's method,
then the Lang–Weil dimension induction, uniformly in families. It does not use Deligne's Weil II,
étale cohomology, the trace formula or weights. All Lean names below are in namespace
`Langlands.AlgebraicGeometry.LangWeil`, and all modules are under
`Langlands/AlgebraicGeometry/LangWeil/`. The registered sources are
`schmidt-1973-zur-methode-von-stepanov` (Schmidt 1973), `lang-weil-1954-number-of-points`
(Lang–Weil 1954), `tao-2012-lang-weil-bound` (Tao 2012),
`stacks-bertini-theorems-0g4c-0fd4-2026-11-09` (Stacks) and
`conrad-2011-weil-grothendieck-adelic-points` (Conrad 2011).

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
| Conrad 2011, Lemma 4.6 (printed p.12), scheme form, from the family estimate | `UniformLangWeilOfFamilyStatement` / `uniformLangWeilOfFamily` | `UniformLangWeilOfFamilyProof` |

How closely the Schmidt rows follow Schmidt:

- Hilfssatz 3 (printed p.350) is proved in a variant form as `Stepanov.frobeniusIndependence`
  in `Stepanov/FrobeniusIndependence`. Its hypothesis `n·d + m(n−1)² < q` is Schmidt's
  inequality (16) on printed p.351. Schmidt's degree bound `q/n − mn` implies it.
- Hilfssätze 1–2 and 4 are not formalized as stated. Resultants replace Schmidt's norms and
  symmetric functions. Power-series branches (`Stepanov/Taylor`, `Stepanov/Branch`,
  `Stepanov/PointBranch`) replace Hilfssatz 4.
