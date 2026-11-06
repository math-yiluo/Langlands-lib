# Conjugating a supplied maximal split torus into a rational Levi

Author: Worker 1340.

This internal derived module applies to a connected reductive group `G` over
an arbitrary field, an actual parabolic `p : P → G`, a supplied rational Levi
`l : L → P`, and an ambient maximal split torus `i : T → G` contained in `P`
on all test schemes. It assumes the two published propositions
`ParabolicDynamicStatement` and `SmoothMaximalSplitTorusConjugacyStatement`.
It does not prove either proposition.

`ParabolicLeviTorus.pointAndFactor` returns an actual point `x : P(k)` and a
group scheme homomorphism `a : T → L`, bundled with the equality

```lean
a ≫ l ≫ p = i ≫ (G.innerIso (rationalPoints.map p x)).hom
```

Thus conjugation by the image of `x` moves the supplied torus into the supplied
Levi. The torus source is the original `T`; any change of source from torus
conjugacy is absorbed into `a`. The bundle is selected noncomputably from
`exists_point_and_factor`, which proves the same existence result.

The preliminary theorem `exists_maximalSplitTorus_factor` only assumes
`ParabolicDynamicStatement` and produces some ambient maximal split torus
factoring through the supplied Levi.

The proof is a deduction from the named Library results, rather than a separate
claim about an original source. First,
`DynamicLeviConjugacy.exists_cocharacter_parabolic_levi` simultaneously
realizes the supplied parabolic and Levi by one cocharacter. Its geometric
radical input is discharged by
`dynamicGeometricUnipotentRadical_of_centralizer dynamicCentralizerReductive`.
The theorem `cocharacterMaximalSplitTorus` extends that cocharacter to an
ambient maximal split torus, and `Dynamic.torusFactor` factors this torus
through the represented dynamic centralizer, namely the supplied Levi.

Next, `IsMaximalSplitTorus.exists_lift` lifts the original torus to `P`.
The theorem
`exists_parabolic_innerIso_comp_eq_of_structuralStatements` conjugates the
two ambient maximal split tori by a point of `P`. Its connectedness input is
the published `dynamicConnected`. Finally,
`comp_innerIso_hom_comp` transports that equality from `P` to `G`, and the
torus isomorphism is composed with the chosen Levi factor.

All containments and equalities used in this argument are equalities of group
scheme maps or containments of subgroup functors on every test scheme. There
are no assumptions about the field being infinite or perfect.
