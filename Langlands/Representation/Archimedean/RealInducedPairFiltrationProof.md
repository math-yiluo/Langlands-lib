# Proof of `RealInducedPairFiltrationStatement`

Lean module: `Langlands.Representation.Archimedean.RealInducedPairFiltrationProof`, namespace
`Langlands.Archimedean`.

## Result

`realInducedPairFiltration : RealInducedPairFiltrationStatement`.

The statement is the Library's `Langlands.Archimedean.RealInducedPairFiltrationStatement`
(module `RealRankOneStepFiltration`). Write `S(ds)` for the `O(n)`-finite functions
`kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)`. Take `n : ℕ`, lists
`pre post : List RealBlock` and blocks `x y : RealBlock` such that:

* `x` or `y` is an induction block `RealBlock.induced d`;
* `realRank (pre ++ x :: y :: post) = n`;
* `realBlockExponent x < realBlockExponent y`.

Then `RealAdjacentFiltration n pre post x y` holds. So there are `k : ℕ`, lists
`ws : Fin k → List RealBlock` and `ℂ`-linear maps `q j : S(pre ++ ws j ++ post) →
S(pre ++ x :: y :: post)` with three properties:

* each `ws j` is either `[y, x]`, or its exponent support is a permutation of that of `[x, y]`
  and its weight square sum is strictly larger;
* each `q j` is an intertwiner modulo the span of the ranges of the `q i` with `i < j`;
* the ranges of all the `q j` span `S(pre ++ x :: y :: post)`.

The theorem has no hypotheses beyond the statement's own.

## Declaration

The theorem is one application of the Library theorem
`realInducedPairFiltration_of_base` (module `RealInducedPairFiltrationReduction`):

```
realInducedPairFiltration_of_base hS hCI hIC hII : RealInducedPairFiltrationStatement
```

Each of its four hypotheses is supplied by a Library theorem.

| Hypothesis | Statement | Library proof (module) |
| --- | --- | --- |
| `hS` | `RealAdjacentFiltrationInStagesStatement` | `InductionStages.realAdjacentFiltrationInStages` (`RealInductionStagesFiltration`) |
| `hCI` | `RealCharacterInducedFiltrationStatement` | `RealCharacterInducedFiltrationProof.realCharacterInducedFiltration` (`RealCharacterInducedFiltrationProof`) |
| `hIC` | `RealInducedCharacterFiltrationStatement` | `RealInducedCharacterFiltrationProof.realInducedCharacterFiltration` (`RealInducedCharacterFiltrationProof`) |
| `hII` | `RealInducedInducedFiltrationStatement` | `realInducedInducedFiltration` (`RealInducedInducedFiltrationProof`) |

The four statements are defined in `RealInducedPairFiltrationReduction`.

## Route of the whole proof

1. **Reduction** (`realInducedPairFiltration_of_base`). By induction in stages (`hS`) it is
   enough to find the filtration for the pair `[x, y]` alone, on `GL_r(ℝ)` with
   `r = realRank [x, y]` and `pre = post = []`. A case split on `x` and `y` then gives one of
   three base cases. Two characters cannot occur, because one block is an induction block.
   * A character followed by an induction block, on `GL₃(ℝ)` (`hCI`).
   * An induction block followed by a character, on `GL₃(ℝ)` (`hIC`).
   * Two induction blocks, on `GL₄(ℝ)` (`hII`).

   In each case the exponent hypothesis of the target is the one the base statement needs.
2. **Induction in stages** (`InductionStages.realAdjacentFiltrationInStages`, Task 7068).
   Let `q j` be the maps of a filtration on `GL_r(ℝ)`. The maps on `GL_n(ℝ)` are
   `Q j = ind (avg (q j))`, with the same lists `ws j`.
   * `avg` averages `q j` over `O(r)` against the normalized Haar measure. This makes it
     exactly `O(r)`-equivariant, and changes it only modulo the earlier filtration step.
   * `ind T` sends `F` to the function whose value at `κ ∈ O(n)` is `(T σ_κ F)(1)`. This
     function is extended from `O(n)` by `PrincipalSeriesExtension.extension`. Here `σ_κ` is
     the slice along the middle block embedding `GL_r → GL_n`.
   * `ind T` lies in the standard module and is `O(n)`-finite. It commutes exactly with `O(n)`,
     and its derivative defect has all slices in the defect subspace on `GL_r(ℝ)`.
   * Induction on the filtration index shows that the ranges of the `Q j` span the target.
     This uses linear sections, averaged over `O(r)`.

   The helper modules are `RealInductionStagesFamily`, `RealInductionStagesAverage`,
   `RealInductionStagesSlice`, `RealInductionStagesFourier`, `RealInductionStagesInduce` and
   `RealInductionStagesDerivative`.
3. **Base cases on `GL₃(ℝ)`** (Tasks 7133 and 7134). The two orders of a character and an
   induction block are proved by a case analysis on the weight of the induction block and the
   difference of the exponents. The maps are block Frobenius intertwining operators. Landing
   statements, proved with an explicit chart integral and transported by a mirror symmetry,
   show that these maps send standard modules into standard modules. The resonant cases also
   use the uncertainty principle `RealOrthogonalUncertainty.realOrthogonalBlockUncertainty`
   and the `K`-type count of module `RealKTypeTransport`.
4. **Base case on `GL₄(ℝ)`** (Task 7135). If one weight is zero, the proof uses the zero-weight
   theorems. These split the weight-zero block into two characters and reuse the `GL₃(ℝ)`
   filtrations through induction in stages. For nonzero weights there are two cases.
   * No linked index: the exact swap intertwiner gives the filtration.
   * A linked index: the proof splits by the sign of the inner weight. These cases use a
     polynomial braid identity, quotient descent, or a decomposition of the crossed quotient
     kernel.

Each module named above has its own paired Markdown file, which states its results and
explains its proofs. None of these proofs uses the Langlands classification or a
composition series as a hypothesis. Every prerequisite is a proved Library theorem. The
theorem depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.
