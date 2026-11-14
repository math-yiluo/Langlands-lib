# Geometric conjugators between presentations exist over a separable closure

Author: Worker 149 (Task 6302). This is a helper module for the proof of
`Langlands.GroupScheme.AlgebraicFundamentalGroup.AlgebraicFundamentalGroupComparisonStatement`
in `Langlands.GroupScheme.AlgebraicFundamentalGroupComparisonProof`. It supplies the
existence input `hA` of
`Langlands.GroupScheme.AlgebraicFundamentalGroup.Choice.comparison_of_conjugators`.

## Statements

Throughout, `k` and `E` are fields in universe `u` with `[Algebra k E]` and
`[IsSepClosure k E]`. Base change is along `algebraBaseMap k E`. Names are in
`Langlands.GroupScheme.AlgebraicFundamentalGroup`.

- `isSplitTorus_baseChange_of_isSepClosure T hT`: if `T` is a commutative group scheme over
  `Spec k` whose underlying group is a torus (`IsTorus T.toGrp`), then its base change to
  `E` is a split torus.
- `Choice.isMaximalSplitTorus_baseChange hG a`: if `G` is connected reductive and
  `a : Choice k G`, then the base change of the chosen maximal torus inclusion
  `(i_a)_E : (T_a)_E ⟶ G_E` is a maximal split torus (`IsMaximalSplitTorus`).
- `Choice.exists_isConjugationComparison E hG a b`: if `G` is connected reductive, then for
  any two presentations `a b : Choice k G` there are a point `g ∈ G_E(E)` and an
  isomorphism `e : (T_a)_E ≅ (T_b)_E` with `a.IsConjugationComparison E b g e`, i.e.
  `(i_a)_E ≫ int(g) = e ≫ (i_b)_E`.

## Provenance

These are internal lemmas. They give the standard facts used in Kaletha–Prasad (2023),
Construction 11.3.1 (printed p. 427, PDF p. 458): over a separable closure, tori split
and any two maximal tori are conjugate by a rational point. No literature statement is
claimed for the Lean declarations; every step is a published Library theorem.

## Proofs

- `isSplitTorus_baseChange_of_isSepClosure`: `torusFiniteGaloisSplitting`
  (`Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof`) splits `T` over a finite Galois
  extension `K` of `k`. `IsSepClosed.lift` embeds `K` into `E` over `k`. The base change
  to `E` factors through `K` (`GroupScheme.baseChangeCompIso`), and splitting is preserved
  by base change (`IsSplitTorus.baseChange`) and isomorphism (`IsSplitTorus.of_iso`).
- `isMaximalSplitTorus_baseChange`: `maximalTorusBaseChange`
  (`Langlands.GroupScheme.Torus.MaximalBaseChangeProof`) shows that the base change of the
  maximal torus is a maximal torus. A split maximal torus is a maximal split torus
  (`IsMaximalTorus.isMaximalSplitTorus`,
  `Langlands.GroupScheme.Torus.MaximalSplitComparison`). Splitting comes from the previous item.
- `exists_isConjugationComparison`: `G_E` is connected reductive, smooth and affine
  (`connectedReductiveFieldExtensionStatement`,
  `Langlands.GroupScheme.Reductive.FieldExtensionProof`). Conjugacy of maximal split tori
  of smooth connected affine groups (`smoothMaximalSplitTorusConjugacy`,
  `Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof`) applies to the
  two maximal split tori of the previous item. It gives a point `g` and a group
  isomorphism of the tori, which `CommGroupScheme.isoOfGroupIso`
  (`Langlands.GroupScheme.Torus.SplitLatticeBaseChange`) turns into an isomorphism
  of commutative group schemes.
