# Proof: the local modular character is the normalized absolute value of `det Ad`

Module `Langlands.Global.LocalModularCharacterAdjointDeterminantProof`.

## Statement proved

`Langlands.Global.PlaceGroupPoints.localModularCharacterAdjointDeterminant` proves the Library
proposition
`Langlands.Global.PlaceGroupPoints.LocalModularCharacterAdjointDeterminantStatement.{u}` at an
arbitrary universe `u`. The setting is:

- `F` is a number field;
- `G` is a smooth affine group scheme of finite type over `Spec F`;
- `i` is a place of `F`, with completion `F_i = placeCompletion F i`;
- `g` is a point of `PlaceGroupPoints F G i = G(F_i)`.

The proposition says that the modular character `Measure.modularCharacter g` of the locally
compact group `G(F_i)` equals the normalized absolute value
`AdelicGroupPoints.localCharacterNorm F G (adjointDeterminantCharacter G).toMul i g` of the
adjoint determinant character at `g`. Write `Δ(g)` for the first side and `N(g)` for the second.
For a finite place, `N(g)` is the normalized absolute value of `det Ad(g)`. For a real place it
is `|det Ad(g)|`, and for a complex place it is `|det Ad(g)|²`.

## Structure of the proof

The proof shows only the upper bound `Δ(g) ≤ N(g)` for every `g`, as
`modularCharacter_le_localCharacterNorm`. Equality then follows from multiplicativity. Both `Δ`
and `N` are monoid homomorphisms, so `Δ(g) Δ(g⁻¹) = 1` and `N(g) N(g⁻¹) = 1`. Hence

`N(g) = N(g) Δ(g) Δ(g⁻¹) ≤ N(g) Δ(g) N(g⁻¹) = Δ(g)`,

using the bound at `g⁻¹`. Together with the bound at `g`, `le_antisymm` gives equality.

### The upper bound at one place

`modularCharacter_le_localCharacterNorm` splits into the archimedean and the finite case.

- **Infinite place `w`.** Mathlib gives `w.Completion` only a `NormedField` instance. The
  proof uses the existing local structure
  `Langlands.AlgebraicGeometry.PointTopology.infiniteCompletionNontriviallyNormedField`.
  It retains the original norm and proves nontriviality using the norm of `2` through the
  isometric embedding `InfinitePlace.Completion.extensionEmbedding`.
  `exists_normedSpace_real_infiniteCompletion` (helper `PlaceGlue`) gives a finite-dimensional
  real normed space structure, so the completion is proper (`FiniteDimensional.proper_real`).
  The proof then applies `modularCharacter_le_of_adjoint_real` (helper `AdjointBound`).
- **Finite place `v`.** The completion `FiniteCompletion F v` gets the nontrivially normed field
  structure `Valued.toNontriviallyNormedField` of its rank-one valuation. Its norm is the
  Mathlib norm of the adic completion, and it is ultrametric. It is locally compact
  (`placeCompletion.locallyCompactSpace`), hence proper (`ProperSpace.of_locallyCompactSpace`).
  The proof then applies `modularCharacter_le_of_adjoint_ultrametric` (helper `AdjointBound`).

In both cases the point group is identified with `G.affinePoints (CommAlgCat.of F K)`, `K` the
completion. The Library instances on `PlaceGroupPoints F G i` give its local compactness,
Hausdorff property, second countability and Borel structure. These instances agree
definitionally with the ones `AdjointBound` expects. The remaining hypothesis of `AdjointBound`
is about Haar scaling: every linear automorphism `A` of `K^d` with `det A = det Ad(g)` scales
additive Haar measure by `N(g)`. This is
`addEquivAddHaarChar_placeLinear_eq_localCharacterNorm` (helper `PlaceGlue`).

## Helper modules

All helpers live in `Langlands/Global/LocalModularCharacter/` and each has its own Markdown
file. They are internal infrastructure. The underlying mathematics is the standard fact that
the modular character of the analytic group `G(K)` is `|det Ad|_K`, proved here without
invariant differential forms.

- `ComparisonMeasure`: the abstract measure-theoretic skeleton. On a second-countable locally
  compact group, a comparison measure that is almost invariant under small left translations,
  and nearly scaled by `D` under conjugation by `g`, bounds `Δ(g) ≤ D`. The proof uses
  uniqueness of Haar measure for the convolution of Haar measure with the comparison measure.
- `LocalScaling`: local Haar-measure estimates on `K^d` for maps with a given derivative at a
  point. The ultrametric case uses isometric bijections of small balls; the real case uses
  Mathlib's change-of-variables estimates.
- `ChartComparison`, `ChartEstimates`: transport these estimates through a chart at the identity
  whose group law has derivative `(a, b) ↦ a + b`. They give `Δ(g) ≤` the Haar scaling factor
  of the derivative of conjugation by `g` in the chart.
- `RegularFamily`: families of points whose regular-function values lie in a subalgebra, such
  as functions that are strictly differentiable at a point. These are points of `G` over that
  subalgebra, so the class is stable under products and inverses.
- `RegularChart` (Worker 1402): a chart of the algebra-point space near a point, from a standard
  smooth presentation and the inverse function theorem.
- `ChartLie`: identifies the derivative of conjugation in such a chart with the adjoint action
  on the Lie kernel. In particular the two determinants agree.
- `IdentityChart`: combines `RegularChart` and `ChartLie` into an identity chart of `G(K)` with
  the derivative properties used by `ChartEstimates`.
- `AdjointBound`: the bound `Δ(g) ≤ c` whenever every linear automorphism with determinant
  `det Ad(g)` scales Haar measure by `c`, in the ultrametric and the real case.
- `HaarScaleNorm` (Worker 1402): Haar scaling of linear automorphisms of `F_i^d` is the
  normalized absolute value of the determinant.
- `PlaceGlue` (Worker 1402): the place-level glue used above.
