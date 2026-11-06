# Borel subgroups from regular cocharacters: proof

Module `Langlands.GroupScheme.Absolute.RegularCocharacterBorelProof`. It proves the published
proposition `Langlands.GroupScheme.RegularCocharacterBorelStatement` (module
`Langlands.GroupScheme.Absolute.BorelStatement`) at its original universe `u`, for task
`618cd683-cfcd-43a3-b4bf-6c8abd208b1f`.

## Statement

`theorem regularCocharacterBorel : RegularCocharacterBorelStatement.{u}`. Let `k : Type u` be a
field, `G` a connected reductive group scheme over `Spec k`, and `j : T.toGrp ⟶ G` a split
maximal torus. Then all three clauses of the target hold:

1. for every cocharacter `ν` of `T` that is regular for `j`, every closed subgroup
   `i : B ⟶ G` representing the dynamic parabolic `P(ν ≫ j)` is a Borel subgroup of `G`;
2. for cocharacters `ν` and `ν'` that are regular for `j`, `P(ν ≫ j) = P(ν' ≫ j)` holds exactly
   when `0 < ⟨α, ν⟩ ↔ 0 < ⟨α, ν'⟩` for every root `α` of `j`;
3. every Borel subgroup `i : B ⟶ G` through which `j` factors (`f ≫ i = j`) represents
   `P(ν ≫ j)` for some cocharacter `ν` of `T` that is regular for `j`.

The theorem has no hypotheses beyond those of the target statement.

## Proof

The proof is one line. It applies the assembly
`regularCocharacterBorelStatement_of_relativeRootNegation` (module
`Absolute.RegularCocharacterBorel`) to the Library proof `relativeRootNegation`
(module `Rational.RelativeRootNegationProof`) of `RelativeRootNegationStatement`. That statement
says that the relative roots of a maximal split torus of a connected reductive group are stable
under negation.

The assembly uses this negation input together with the following Library proofs:

- `dynamicLie`, `dynamicSmooth`, `dynamicConnected`;
- `lieSubgroupEquality`;
- `rankOneSolvableObstruction`;
- `borelConjugacy`, `maximalTorusConjugacy`;
- `connectedReductiveFieldExtensionStatement`, `maximalTorusBaseChange`;
- `genericCentralizer`, `maximalTorusCentralizer`, through the solvability lemma
  `isSolvableGroupScheme_of_isRepresentedBy_parabolic_of_isRegular`.

The Markdown of the five supporting modules describes how the clauses are proved:

- `RegularCocharacterMaximal`: maximality in clause 1, via the Lie-algebra criterion and the
  rank-one obstruction;
- `RegularCocharacterParabolic`: clause 2;
- `RegularCocharacterDescent` and `RegularCocharacterBaseChange`: clause 3, by passing to the
  algebraic closure and descending the cocharacter;
- `RegularCocharacterBorel`: the assembly.

## Provenance

Milne, *Algebraic Groups* (Cambridge, 2017):

- clause 1 is Proposition 21.29 (printed p.433, PDF p.449);
- clauses 2 and 3 are Theorem 21.32 and its proof (printed pp.434–435, PDF pp.450–451).

The Lean route differs from Milne's in the ways described in the supporting modules' Markdown.

## Authorship

Workers 1234 and 303. Worker 303 wrote the Library modules
`Absolute.RegularCocharacterWeights`, `Dynamic.UnipotentSolvable`,
`Absolute.RegularCocharacterSolvable` and `Absolute.MaximalTorusCentralizerProof`, which the
supporting modules use.
