# Proof: the algebraic-space form of Conrad's Lemma 4.6 from the scheme estimates in families

Authors: Worker 75 and Worker 3694 (module `SpaceFamily.FiniteFieldCharts`). The chart
construction in `SpaceFamily.SeparatedChart` follows Worker 80's draft for Task 5417.

This module proves the published statement
`Langlands.AlgebraicGeometry.LangWeil.SpaceUniformLangWeilOfFamilyStatement` with the theorem
`Langlands.AlgebraicGeometry.LangWeil.spaceUniformLangWeilOfFamily`. It imports the statement's
Lean/Markdown pair unchanged and adds no hypotheses. The two antecedents of the implication,
`FamilyLangWeilStatement` and `FamilyPointUpperBoundStatement`, are the only estimates used. No
other Lang–Weil, Hasse–Weil, Weil-conjecture or Bertini input enters as a hypothesis, axiom or
structure field. Everything else is proved in the helper modules
`Langlands/AlgebraicGeometry/LangWeil/SpaceFamily/*` or taken from the Library.

## The theorem

Let `f : Y → B` be a morphism of algebraic spaces over `Spec (ULift ℤ)` with the hypotheses of
`SpaceUniformLangWeilStatement`. These are: `B` quasi-separated and of finite type over `ℤ`;
an étale chart square `a : U → Y`, `b : V → B`, `φ : U → V` with `a` surjective and `φ` smooth
of relative dimension `d`; and `f` separated, quasi-compact and surjective with geometrically
connected fibres. The proof has two steps.

1. `SpaceFamily.FiniteFieldCharts.exists_finiteField_charts` gives finitely many affine
   schemes `M i`, locally
   of finite type over `ℤ`, with étale morphisms `t i : h(M i) → B`. Every point of `B` with
   values in a finite field `κ` is `h(m) ≫ t i` for some `i` and some `m : Spec κ → M i`.
2. `SpaceFamily.spaceUniformLangWeil_of_charts` turns these charts into the conclusion of
   `SpaceUniformLangWeilStatement`: one constant `C > 0` with
   `|#{y ∈ Y(κ) | f(y) = x} − (#κ)^d| ≤ C (#κ)^(d − 1/2)` for all finite fields `κ` and all
   `x ∈ B(κ)`. The étaleness of the `t i` is not needed.

## Route through the helper modules

The statement's Markdown records the expected route: stratify by schemes, count the top
stratum with the Lang–Weil estimate in families, and bound the lower strata with the upper
bound. The implementation follows it as below. Each module's Markdown describes its proofs.

- `SpaceFamily.FieldPoints`: field points of schemes and of functors of points over the
  terminal base `Spec (ULift ℤ)`; Galois descent of points; lifting of points along
  surjective maps and closed immersions.
- `SpaceFamily.FiniteFieldCharts` (step 1): scheme charts of `B` through which all points with
  values in finite fields factor. A point over `κ` lifts to the étale atlas of `B` over a
  finite extension `L/κ`, with pairwise distinct Galois conjugates. The cyclic group
  `Aut(L/κ)` then gives an invariant point of a quotient chart of a fibre power of the atlas,
  which descends to `κ`. The number of quotient charts is finite because the fibres of the
  atlas are uniformly bounded.
- `SpaceFamily.SeparatedChart`: for a separated algebraic space `X` with an affine étale
  surjective chart, the symmetric tuple quotients `V_n` with étale maps `V_n → X`.
- `SpaceFamily.DegreePoints` and `SpaceFamily.Counting`: every point of `X` with values in a
  finite field `κ` comes from exactly one point of exactly one degree scheme `D_n` over
  `V_n`, so `#X(κ)` over a point of the base is `∑_{n < N} #D_n(κ)`.
- `SpaceFamily.FibreCharts` and `SpaceFamily.Strata`: the fibres of `V_n` over the base are
  geometrically irreducible of dimension `d` on the stratum where `n` is maximal, and the
  fibres of `D_n` have dimension below `d` over the higher strata.
- `SpaceFamily.SchemeBase`: the estimate for a separated algebraic space `X` over a scheme
  `M` of finite type over `ℤ`, by stratifying `M` and applying the two statements in families
  to the strata.
- `SpaceFamily.FibreProductBase`: the estimate for `Y` over one scheme chart `t : h_M → B`,
  by applying `SchemeBase` to the fibre product `Y ×_B M`.
- `SpaceFamily.RingPointCharts` (step 2): translation between `RingPoints (ULift ℤ) B κ` and
  morphisms from `h(Spec κ)`, and the sum of the chart constants.
