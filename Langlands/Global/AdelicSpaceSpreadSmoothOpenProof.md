# Proof of Conrad's Theorem 5.9 for separated algebraic spaces

Author: Worker 5254.

`Langlands.Global.adelicSpaceSpreadSmoothOpen` proves the unchanged published
proposition `Langlands.Global.AdelicSpaceSpreadSmoothOpenStatement.{u}` from
`Langlands/Global/AdelicSpaceSpreadMapStatement.lean`, in every universe `u`, with no extra
hypotheses. That statement is Theorem 5.9 of Brian Conrad, *Weil and Grothendieck approaches
to adelic points* (December 31, 2011), printed p.17 (registered source
`conrad-2011-weil-grothendieck-adelic-points`), for global fields of both characteristics:
a smooth surjective map `g : Y ⟶ W` of algebraic spaces over a global field, with
geometrically connected fibres, induces an open map `Y(A) → W(A)` on adelic points, where
`Y(A)` and `W(A)` carry the topologies defined by arbitrary separated models of finite type
over rings of `S`-integers (the two models may invert different sets of places). The objects
are explained in `AdelicSpaceSpreadMapStatement.md`.

## Proof

The proof is the single term

```
adelicSpaceSpreadSmoothOpen_of_langWeil
  (spaceUniformLangWeilOfFamily (familyLangWeilOfPlaneCurve planeCurveHasseWeil)
    familyPointUpperBound)
```

and every name in it is a published Library theorem:

1. `Langlands.Global.adelicSpaceSpreadSmoothOpen_of_langWeil`
   (`Langlands/Global/AdelicSpaceSmoothConnectedSpreadOpen.lean`) proves
   `SpaceUniformLangWeilStatement.{u} → AdelicSpaceSpreadSmoothOpenStatement.{u}`: it
   replaces the supplied models by smooth models with geometrically connected fibres over a
   common ring of `S`-integers, proves the model arrow open on adelic points using the
   uniform Lang–Weil estimate (the algebraic-space form of Conrad's Lemma 4.6), and
   transports openness back to the two supplied topologies.
2. `Langlands.AlgebraicGeometry.LangWeil.spaceUniformLangWeilOfFamily`
   (`Langlands/AlgebraicGeometry/LangWeil/SpaceUniformLangWeilOfFamilyProof.lean`) proves
   `FamilyLangWeilStatement.{u} → FamilyPointUpperBoundStatement.{u} →
   SpaceUniformLangWeilStatement.{u}` by covering the algebraic space by scheme charts.
3. `Langlands.AlgebraicGeometry.LangWeil.familyLangWeilOfPlaneCurve`
   (`Langlands/AlgebraicGeometry/LangWeil/FamilyLangWeilOfPlaneCurveProof.lean`) proves
   `PlaneCurveHasseWeilStatement.{u} → FamilyLangWeilStatement.{u}`, the uniform Lang–Weil
   estimate for geometrically irreducible scheme families in every fibre dimension, by
   induction on the dimension (zero-dimensional case, curve case, hyperplane slicing with
   the proved generic Bertini theorem).
4. `Langlands.AlgebraicGeometry.LangWeil.planeCurveHasseWeil`
   (`Langlands/AlgebraicGeometry/LangWeil/PlaneCurveHasseWeilProof.lean`) proves
   `PlaneCurveHasseWeilStatement.{u}`, Schmidt's elementary Hasse–Weil bound for absolutely
   irreducible plane curves (W. M. Schmidt, *Zur Methode von Stepanov*, Acta Arith. 24
   (1973), Satz, printed p.347), by Stepanov's method.
5. `Langlands.AlgebraicGeometry.LangWeil.familyPointUpperBound`
   (`Langlands/AlgebraicGeometry/LangWeil/FamilyPointUpperBoundProof.lean`) proves
   `FamilyPointUpperBoundStatement.{u}`, the uniform bound `C (#κ)^e` on point counts in
   families.

Feeding 4 into 3 gives `FamilyLangWeilStatement.{u}`; with 5, step 2 gives
`SpaceUniformLangWeilStatement.{u}`; step 1 then gives the target. All universes are the
same `u`.

## Assumptions

No Lang–Weil, Hasse–Weil, Weil-conjecture or Bertini input is assumed as a hypothesis,
axiom or structure field: each is proved in the Library modules listed above. The
development check of this module reports only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.
