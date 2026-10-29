# JPS decomposition assembly from uniform coordinate dilations (proof)

## Result

Module `Langlands.Representation.Whittaker.JPSDilationAssemblyProof` proves

```lean
theorem Langlands.Whittaker.jpsDilationAssembly : JPSDilationAssemblyStatement.{uF}
```

which is the published proposition
`Langlands.Whittaker.JPSDilationAssemblyStatement.{uF}` from
`Langlands.Representation.Whittaker.JPSDilationAssemblyStatement`, unapplied and
with its single universe parameter `uF`. The proof starts with
`intro p _ F T n W Y A hLC hUS hFF hD`, so it covers every prime `p`, every
`F : PadicField.{uF} p`, every `T : F.TopologicalData` (with `T.topology`),
every `n` including `n = 0`, and every `W`, `Y`, `A`. It uses exactly the four
hypotheses of the statement: local constancy (`hLC`), coordinate upper support
(`hUS`), the finite-function property of every `η ∈ Y i` (`hFF`), and the
uniform bounded dilation formula (`hD`). Nothing else is assumed: there is no
commutation of the `A i η`, no finite-dimensionality of `W`, and no common
stabilizer. Every auxiliary declaration is in the namespace
`Langlands.Whittaker.JPSDilationAssembly`. The proof contains no `sorry` and no
new axioms; `lean_check` reports only `propext`, `Classical.choice` and
`Quot.sound`.

Notation: `|y|` is `T.normalizedAbs y`, and for a torus point `a` we write
`ι a = fun i => (a i : F.Carrier)` for the corresponding point of the additive
space `Fⁿ = Fin n → F.Carrier`.

## How `X` is chosen before `f`

For each coordinate `i`, `transSpan (Y i)` is the complex span of the constant
function `1` and of all left translates `y ↦ η (b * y)` with `η ∈ Y i` and
`b ∈ Fˣ`. Three facts about it are proved:

- `translate_mem_of_mem`: it is stable under left translation. The proof checks
  the generators and uses the linear map `LinearMap.funLeft` of precomposition
  with `y ↦ b * y`. The translate of a translate of `η` by `b'` is the translate
  by `b' * b`.
- `continuous_of_mem_transSpan`: each member is continuous on `Fˣ`. The proof
  is by span induction, from the continuity part of `hFF` and the continuity of
  multiplication on the units.
- `fg_transSpan`: it is finitely generated. It lies in
  `span {1} ⊔ ⨆_{η ∈ Y i} span (translates of η)`. Each summand is finitely
  generated because of the finite-dimensionality part of `hFF`
  (`Submodule.fg_iff_finiteDimensional`, `Submodule.fg_finset_sup`,
  `Submodule.fg_span_singleton`), and over `ℂ` a submodule of a finitely
  generated submodule is finitely generated (`Submodule.FG.of_le`).

The closing theorem chooses (`choose B hB`) finite sets `B i` with
`span (B i) = transSpan (Y i)`. Then
`X := (Fintype.piFinset B).image prodFun`, where
`prodFun σ a = ∏ i, σ i (a i)`. `X` depends only on `Y` and this choice. It is
fixed before the universally quantified `f` is introduced.

The proof that members of `X` satisfy `IsFiniteFunction T` is
`isFiniteFunction_prodFun`:

- Continuity: `prodFun σ` is a finite product of the continuous functions
  `σ i` composed with the coordinate projections (`continuous_finsetProd`).
- Finite-dimensional translates: the translate `a ↦ prodFun σ (b * a)` is the
  product of the one-coordinate translates `y ↦ σ i (b i * y)`. These lie in
  `transSpan (Y i) = span (B i)`. Lemma `prod_expand` then writes the product as
  a linear combination of the `prodFun σ'`, `σ' ∈ piFinset B`, so it lies in
  `span X`. Hence the span of all translates is contained in the
  finite-dimensional `span X` (`Submodule.finiteDimensional_of_le`).

`prod_expand` writes each `τ i ∈ span (B i)` as `∑_{β ∈ B i} w i β • β`
(`Submodule.mem_span_finset`). It distributes the product over the sums
(`Finset.prod_univ_sum`) and takes `κ σ = ∏ i, w i (σ i)`.

## The stage functions and one coordinate step

For finite sets `S` (unprocessed coordinates) and `J` (coordinates frozen at a
small value), thresholds `r : Fin n → ℝ`, one-coordinate functions `γ`, a torus
point `c` and a function `g`, the stage function is

```
term S J r γ c g a = (∏ i, factor i (a i)) * g (freeze J c a).
```

Here `freeze J c a` replaces the coordinates in `J` by those of `c`. The factor
`factor i y` is

- `γ i y` if `|y| ≤ r i`, and `0` otherwise, for `i ∈ J`;
- `1` for `i ∈ S`;
- `1` if `r i < |y|`, and `0` otherwise, for any other `i`.

`term_univ` shows that `term univ ∅ 1 1 1 g = g`.

`term_insert` processes one coordinate `i ∉ S ∪ J` for `g ∈ W`. Let `ε` be the
threshold that `hD` gives for `i` and this `g`, and let `c_i` be a unit with
`|c_i| < ε`. Such a unit exists by `exists_unit_normalizedAbs_lt`: a power of
the uniformizer works, since `|ϖ| = q⁻¹` with `q > 1`. Coordinate `i` splits
into two cases.

- **Large, `|c_i| < |a_i|`.** `g` is kept, and the factor of `i` becomes the
  cutoff `|a_i| > |c_i|`.
- **Small, `|a_i| ≤ |c_i|`.** Put `b = c_i⁻¹ a_i`, so `|b| ≤ 1`, and let
  `a' = freeze (insert i J) (update c i c_i) a`. Then `a'_i = c_i`, so
  `|a'_i| < ε`, and `a' * coordinateEmbedding i b = freeze J c a`
  (`mul_coordinateEmbedding`). By `coordinateRepresentation_apply`, `hD` gives
  `g (freeze J c a) = ∑_{η ∈ Y i} η (c_i⁻¹ a_i) * (A i η g) a'`.

Hence, with `r' = update r i |c_i|`,

```
term (insert i S) J r γ c g
  = term S J r' γ c g
    + ∑_{η ∈ Y i} term S (insert i J) r' (update γ i (η (c_i⁻¹ * ·))) (update c i c_i) (A i η g).
```

The new one-coordinate function `η (c_i⁻¹ * ·)` is a translate of `η`, so it
lies in `transSpan (Y i)`.

## The induction

`term_induction` is purely algebraic. Let `E` be any predicate on functions
that holds for `0` and is closed under addition, and suppose `E` holds for
every terminal term (`S = ∅`) with all `r i > 0` and with
`γ i ∈ transSpan (Y i)` for `i ∈ J`. Then `E` holds for every term with `J`
disjoint from `S`. The proof is by `Finset.induction_on` over `S`. In each step,
`ε` and `c_i` are chosen by `hD` for the function `g` of that term, which is
either the original `f` or some `A i η g ∈ W`. So no threshold common to
several functions is ever needed, and the thresholds `r` stay positive because
`|c_i| > 0`.

## Coefficients on all of `Fⁿ`

For a terminal term, `term_empty_eq` gives

```
term ∅ J r γ c g a = boxCoeff J r c g (ι a) * ∏ i, (if i ∈ J then γ i else 1) (a i).
```

The coefficient `boxCoeff J r c g : Fⁿ → ℂ` is defined on the whole additive
space as follows.

- `box J r` is the set of `x ∈ Fⁿ` with `|x_i| ≤ r i` for `i ∈ J` and
  `r i < |x_i|` for `i ∉ J`.
- On `box J r`, `boxCoeff J r c g x = g (fill J c x)`, where `fill J c x` has
  coordinate `c i` for `i ∈ J` and `unitOf (x i)` otherwise. `unitOf y` is `y`
  as a unit when `y ≠ 0`, and `1` when `y = 0`.
- Off the box, `boxCoeff` is `0`.

In particular, points on coordinate hyperplanes are handled explicitly. If
`x_i = 0` for some `i ∉ J`, then `x` is not in the box, because `r i > 0`, so
the coefficient is `0`. For `i ∈ J`, `x_i = 0` is allowed, and `fill` does not
read `x_i`.

`boxCoeff_mem` proves, for `g ∈ W` and all `r i > 0`, that `boxCoeff` lies in
`HarmonicAnalysis.schwartzBruhatSubmodule (Fin n → F.Carrier)` for the product
topology induced by `T.topology`.

- **The box is clopen** (`isClopen_box`). Each closed ball `{y | |y| ≤ ρ}` with
  `ρ > 0` is closed, by continuity of `T.normalizedAbs`. It is also open
  (`isOpen_le`): by the ultrametric inequality it contains the open set
  `{z | |z - y| < ρ}` around each of its points. Its complement is the
  large-coordinate condition. The box is a finite intersection of preimages
  under coordinate projections.
- **Local constancy.** Off the box, `boxCoeff` vanishes on the open complement.
  At a point `x` of the box, the coordinates `x_i` with `i ∉ J` are nonzero.
  `unitOf` is continuous at nonzero points (`continuousAt_unitOf`, via
  `Units.isEmbedding_val₀`), so `fill J c` is continuous at `x`. Since `g` is
  locally constant (`hLC`), `g ∘ fill J c` is eventually constant near `x`, and
  so is `boxCoeff` on the open box.
- **Compact support.** `hUS` gives `R i > 0` with `g a = 0` whenever
  `R i < |a_i|`. The support lies in the closed set `∏ i {y | |y| ≤ ρ i}`, with
  `ρ i = r i` for `i ∈ J` and `ρ i = R i` for `i ∉ J`. Outside it, some `|x_i|`
  exceeds `ρ i`. If `i ∈ J`, then `x` is not in the box. If `i ∉ J`, then
  `|(fill J c x)_i| = |x_i| > R i`, so `g` vanishes there. Closed balls are
  compact (`isCompact_le`): the ball is a closed subset of the image of the
  compact ring of integers (`T.isCompact_integers`) under multiplication by
  `d⁻¹`, for a unit `d` with `|d| < 1 / max ρ 1`. The product of these balls is
  compact (`isCompact_univ_pi`), and `HasCompactSupport.intro'` applies.

## Expansions and the closing step

`HasExpansion T B h` says that there are functions `Ψ σ ∈ schwartzBruhatSubmodule`
with `h a = ∑_{σ ∈ piFinset B} Ψ σ (ι a) * prodFun σ a` for every torus point
`a`.

- It holds for `0` (`hasExpansion_zero`).
- It is closed under addition, by adding coefficients (`hasExpansion_add`).
- It holds for every terminal term (`hasExpansion_term`). The factors
  `if i ∈ J then γ i else 1` lie in `transSpan (Y i) = span (B i)`, so
  `prod_expand` gives scalars `κ σ`, and `Ψ σ = κ σ • boxCoeff J r c g` works.

The closing theorem applies `term_induction` with `E = HasExpansion T B`,
`S = univ`, `J = ∅`, `r = 1`, `γ = 1`, `c = 1` and `g = f`, and rewrites with
`term_univ`. It then regroups by the value of `prodFun`. The coefficient of
`χ ∈ X` is

```
Φ χ = ∑_{σ ∈ piFinset B, prodFun σ = χ} Ψ σ,
```

a finite sum in the Schwartz–Bruhat submodule. `Finset.sum_fiberwise_of_maps_to`
gives `f a = ∑_{χ ∈ X} Φ χ (ι a) * χ a` at every torus point `a`.

## The case `n = 0`

No case split is needed, and the argument above is uniform in `n`. For `n = 0`:

- `piFinset B` has exactly one element, so `X = {1}`.
- The induction over `S = univ = ∅` is just its terminal case.
- The box is the single point of `F⁰`.
- The coefficient is a function on a one-point space, so it is trivially
  locally constant and compactly supported.

## Relation to the source

JPS (1979), *Automorphic forms on GL(3) I*, printed p.182 (proof of
Lemma (2.2.1)), argues by induction on `n` with one small `c` in the last
coordinate. The implementation instead processes all coordinates in one
induction over the set of unprocessed coordinates, using the uniform-region
hypothesis `hD` in each coordinate. It picks the small unit separately for
each function that occurs, and it builds the coefficients directly as box
functions on `Fⁿ`. The statement Markdown explains how this derived statement
relates to the printed lemma.

## Dependencies

- `Langlands.Representation.Whittaker.JPSDilationAssemblyStatement`: the
  target. Through it, the proof uses:
  - from `Langlands.Representation.Whittaker.JPSFunctionSpace`: `Torus`,
    `FunctionSpace`, `coordinateEmbedding`, `coordinateRepresentation`,
    `coordinateRepresentation_apply`, `mul_coordinateEmbedding`,
    `IsLocallyConstantSpace`, `HasCoordinateUpperSupport` and
    `IsFiniteFunction`;
  - from `Langlands.HarmonicAnalysis.Basic`: `schwartzBruhatSubmodule` and
    `SchwartzBruhat`.
- `Langlands.LocalField.Normalization.Continuity`:
  `TopologicalData.continuous_normalizedAbs`.
- `Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof`:
  `TopologicalData.isCompact_integers`.
- Imported transitively:
  - the normalized absolute value API in
    `Langlands.LocalField.Normalization.Proof`: `normalizedAbs_mul`, `_one`,
    `_zero`, `_pos`, `_nonneg`, `_add_le_max`, `_le_one_iff_mem_integers`,
    `_uniformizer`, `ord_uniformizer`, `ord_zero` and
    `residueCardinality_gt_one`;
  - `TopologicalData.fieldT2` and the `valuativeRel` and `localField`
    structures of `T`. These are installed locally in proofs to obtain the
    topological field structure: continuous multiplication and continuity of
    inversion away from `0`.
- Mathlib: finite-dimensionality and finite generation of submodules, span
  induction, `LinearMap.funLeft`, `Fintype.piFinset` with
  `Finset.prod_univ_sum`, fiberwise sums, clopen sets, `IsLocallyConstant`,
  `HasCompactSupport`, and the topology of units.

None of `JPSDecompositionStatement`, `WhittakerLastEntryOneAsymptoticStatement`,
`WhittakerTypeAsymptoticStatement` or `JPSUniformDilationStatement` is imported
or used.
