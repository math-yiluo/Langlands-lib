# Proof that ambient smooth real homomorphisms annihilate algebraic derived rational points

Author: Worker 4314.

`Langlands.BruhatTits.RationalPoints.derivedSmoothRealAnnihilation` proves the Library
proposition `Langlands.BruhatTits.RationalPoints.DerivedSmoothRealAnnihilationStatement.{u}`
(module `Langlands.BruhatTits.RationalPoints.SmoothRealStructureStatement`). It holds at an
arbitrary universe `u`, and its hypotheses are unchanged. Fix a field `F` with the
nonarchimedean local-field class, in mixed or equal characteristic. Let `M` satisfy
`GroupScheme.IsConnectedReductive M`. Let `f : rationalPoints M →* Multiplicative ℝ` have
kernel open in `rationalPointTopology F M.X`. Then every rational point of the
scheme-theoretic derived subgroup, `(derivedSubgroup M).carrier (Over.mk (𝟙 _))`, lies in
`f.ker`. The open-kernel hypothesis is on the ambient homomorphism `f`. The proof neither
identifies derived points with abstract commutators nor uses rational-point surjectivity of a
central isogeny. It makes no splitting or characteristic restriction. Its axioms are
`propext`, `Classical.choice` and `Quot.sound`.

## Implemented proof

The Lean proof is a single term composing three published Library theorems.

1. `derivedSmoothRealAnnihilation_of_structure` (module
   `Langlands.BruhatTits.RationalPoints.DerivedSmoothRealReduction`) concludes the exact
   target `DerivedSmoothRealAnnihilationStatement.{u}`. Its only premises are the propositions
   `PositivePowerTorusAdditiveFactorizationStatement.{u}` and
   `RelativeRootReflectionExistenceStatement.{u}`.
2. `Langlands.GroupScheme.positivePowerTorusAdditiveFactorization` (module
   `Langlands.GroupScheme.Rational.PositivePowerFactorizationProof`) proves the first premise
   over every field. It splits by characteristic internally.
3. `Langlands.GroupScheme.rootRankOneFactorization` (module
   `Langlands.GroupScheme.Rational.RootRankOneFactorizationProof`) proves
   `RootRankOneFactorizationStatement.{u}` over every field. The adapter
   `Langlands.GroupScheme.relativeRootReflectionExistence_of_rootRankOneFactorization`
   (module `Langlands.GroupScheme.Rational.RootGeneratedCentralizerReduction`) turns it into
   the second premise. It adds no hypothesis beyond the rank-one factorization.

No new lemma is introduced, and no premise remains.

## Actual-point comparisons used inside the reduction

The reduction in step 1 has its own Markdown. The comparisons it uses on actual points are as
follows.

- Derived points are lifted, not identified with commutators. The published
  `derivedSubgroupRepresentability` supplies a closed, affine, locally finite type
  representative `d : D → M` of the algebraic derived subgroup. The published
  `derivedSubgroupSmoothness` makes `D` smooth. The range equality of the representative
  lifts an actual derived rational point `x` to a rational point `y` of `D` with
  `d(y) = x`.
- Factorization in `D`. Step 2, applied to `D` and `y`, gives `m > 0` with
  `y ^ m = i(t) * φ(1)`. Here `i` is a closed torus in `D`, `t` is a rational point of that
  torus, and `φ` is a homomorphism from the one-dimensional vector group. The composite
  closed torus `i ≫ d` has its whole range inside the algebraic derived subgroup of `M`.
- The torus factor. `torusImage_eq_one_of_structure` (module `TorusDerivedSmoothAnnihilation`)
  kills `f(d(i(t)))`. It uses the reflection data from step 3 together with the published
  `Langlands.Plancherel.torusNormKernelCompactness`. A power of the torus point is an actual
  split-torus point times a point of the compact norm kernel. The split part lies in a maximal
  split torus of `M`, and the published split-torus annihilation theorem kills it. Weil's
  finite-range theorem and torsion freeness of `ℝ` kill the norm-kernel part.
- The additive factor. `vectorImage_eq_one` (module `AdditiveSmoothAnnihilation`) kills
  `f(d(φ(1)))`.
- Conclusion. Hence `f(x) ^ m = 1`. Torsion freeness of the additive real group gives
  `f(x) = 1`.

This route does not need `D` to be reductive or semisimple. It uses no rational Jordan
decomposition and no perfectness of `F`.

## Scope

The theorem proves exactly the third component of `SmoothRealStructureStatement`. It does not
prove the central compactness or central-derived cocompactness components. It also does not
prove the final smooth-real descent, which is owned by a separate task.
