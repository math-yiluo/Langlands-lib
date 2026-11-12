# The general semistandard parabolic intersection theorem: proof

Author: Worker 4048.

`Langlands.GroupScheme.dynamicSemistandardIntersection` proves exactly
`Langlands.GroupScheme.DynamicSemistandardIntersectionStatement.{u}` for an
arbitrary universe `u`. Fix a field `k`, a connected reductive group scheme
`G` over `Spec k`, a maximal split torus `i : T → G` and two cocharacters
`α, β` of `T`. Put `χ = α ≫ i` and `ψ = β ≫ i`, and take an arbitrary closed
homomorphism `j : M → G` that represents the dynamic centralizer of `χ`.
The theorem gives all three conclusions of the target:

- the pullbacks along `j` of `P(ψ)`, `Z(ψ)` and `U(ψ)` satisfy
  `SubgroupFunctor.IsParabolicWithLeviAndRadical`;
- `SubgroupFunctor.SemistandardIntersectionProducts` holds for `Z(χ)`, `U(χ)`,
  `P(ψ)`, `Z(ψ)` and `U(ψ)` on every test scheme;
- some maximal split torus `iM : T → M` satisfies `iM ≫ j = i` and has range in
  the pullback of `P(ψ)` along `j`.

The parabolics and Levis are not nested in any way.

## Implemented proof

The proof applies the published conditional reduction
`dynamicSemistandardIntersection_of_structural` from
`Rational.DynamicSemistandardIntersectionModels`. That reduction has exactly
three premises, and each is discharged by a published unconditional theorem:

- `ParabolicDynamicStatement.{u}`, by `parabolicDynamic`
  (`Absolute.ParabolicDynamicProof`);
- `DynamicCentralizerReductiveStatement.{u}`, by `dynamicCentralizerReductive`
  (`Dynamic.CentralizerReductiveProof`);
- `DynamicGeometricUnipotentRadicalStatement.{u}`, by
  `dynamicGeometricUnipotentRadical` (`Dynamic.GeometricUnipotentRadicalProof`).

No other hypothesis is introduced. The final theorem therefore depends only on
the axioms `propext`, `Classical.choice` and `Quot.sound`. The `lean_check`
inspection of the theorem reports exactly these axioms.

Here is how the reduction works. The centralizer theorem makes the closed
representative `M` connected reductive. The second cocharacter lifts through
`j` as `Dynamic.intersectionCocharacter`, and the closed-subgroup comparison
theorems identify the dynamic parabolic, centralizer and identity-limit
functors of this lift with the three pullbacks along `j`. Inside `M`, the
single-cocharacter structural reduction
`Dynamic.isParabolicWithLeviAndRadical_of_structural` assembles the chosen
affine dynamic models of the lift. Their parabolicity comes from the dynamic
characterization of parabolics. The Levi model is connected reductive, and the
identity-limit model is the full geometric unipotent radical. Rewriting along
the three identifications gives the first conclusion. The second conclusion is
the published all-test common-torus theorem
`Dynamic.semistandardIntersectionProducts`. The third is the published
`IsMaximalSplitTorus.exists_lift_to_centralizer_parabolic`.

## Scope and provenance

The field, universe, torus, both cocharacters and the closed representative
are all arbitrary. There is no split, `GL`-only, perfect-field or
characteristic restriction. Every representation, membership and product
condition holds on all test schemes over `k`, including nonreduced ones. The
parabolic-in-Levi conclusion, the radical identification and both products are
proved conclusions, not premises.

This pair composes published Library results internally. It adds no external
structural claim and no citation. The statement pair and the imported
definition pairs are unchanged. Their Markdown records the original sources:
Renard V.3.8 and V.3.10, Borel–Tits 1965 and Milne 2017. The three structural
theorems and the reduction keep their own published pairs, authorship and
proof explanations. Dynamic representability and centralizer reductivity
remain with their independent owners and are only reused here. Standard
cocharacter realization and the nested standard-index proof are neither used
nor replaced by this composition.
