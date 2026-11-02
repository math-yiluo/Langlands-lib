# Serre vanishing for two ample line bundles on a proper scheme over a field: proof

Authors: Worker 716 and Worker 311.

This module proves the published proposition
`Langlands.AlgebraicGeometry.Modules.ProperAmplePairSerreVanishingStatement.{u}` from
`Langlands.AlgebraicGeometry.Modules.ProperAmplePairSerreVanishingStatement`. It imports
that module unchanged.

## Main result

`Langlands.AlgebraicGeometry.Modules.properAmplePairSerreVanishing` is the theorem

```lean
theorem properAmplePairSerreVanishing : ProperAmplePairSerreVanishingStatement.{u}
```

for an arbitrary universe `u`. Unfolded, it says the following. Let `K : Type u` be a
field, `f : X ⟶ Spec K` proper, `M : X.Modules` quasi-coherent with `Γ(M, U)` a finite
`Γ(X, U)`-module for every affine open `U`, and `L₁ L₂ : LineBundle X` ample. Then there
is `n₀ : ℕ` such that

`IsZero ((DerivedSections.relativeCohomology f i).obj (tensorObj (tensorObj M (tensorPow L₁.obj a)) (tensorPow L₂.obj b)))`

for all `a, b ≥ n₀` and all `i > 0`. The theorem has no hypothesis beyond the
statement's. Its axioms are `propext`, `Classical.choice` and `Quot.sound`.

## The proof

The theorem is one line:

```lean
properAmplePairSerreVanishing_of_sectionKilling
  (SerreVanishing.sectionKilling_of_twistKilling SerreVanishing.twistKilling)
```

It composes three results. Each is proved in its own module, with its own Markdown.

1. `SerreVanishing.twistKilling : SerreVanishing.TwistKillingStatement.{u}`
   (module `SerreVanishing.Killing`). Let `X` be proper over a field, `N` locally free
   of rank one and `s` a global section of `N` whose trivialization locus
   `trivializationOpen N s` is affine. Then every class `ξ ∈ H^{p+1}(X, Z)` of a
   quasi-coherent `Z` is killed by multiplication by `s ^ k`,
   `twistPow N s k : Z ⟶ (twistIter N k).obj Z`, for some `k`. This is the Lean form of
   Stacks Lemma 30.17.4, tag [01XR](https://stacks.math.columbia.edu/tag/01XR).
2. `SerreVanishing.sectionKilling_of_twistKilling` (module `SerreVanishing.Adapter`)
   deduces `SerreVanishing.SectionKillingStatement.{u}` (module `SerreVanishing.Twist`).
   Let `G` be coherent, `P` a line bundle and `i > 0`. Suppose that for every `k`, the
   kernel of multiplication by `s` on `G`, twisted by `N^(m+k)` and `P`, has zero
   `H^{i+1}`, and its cokernel, twisted the same way, has zero `H^i`. Then
   `H^i((G ⊗ N^(m+t)) ⊗ P) = 0` for some `t`.
3. `properAmplePairSerreVanishing_of_sectionKilling` (module `SerreVanishing.Assembly`)
   deduces the target from `SectionKillingStatement`.

### Step 1: killing classes by powers of a section

The modules `SerreVanishing.Mul`, `SerreVanishing.Iterate`, `SerreVanishing.Chart`,
`SerreVanishing.Glue`, `SerreVanishing.ChartOf` and `SerreVanishing.Killing` carry out
this step.

- `Iterate` defines the right-nested twists `twistIter N k`. It also defines the natural
  transformations `stepNat N s k`, multiplication by `s`, and `twistPow N s k`,
  multiplication by `s ^ k`. It states `TwistKillingStatement`.
- `Mul` and `Chart` identify the twists `(twistIter N m).obj Z` with `Z` over an open `T`
  on which `N` is trivial (`twistChartIso`). In this identification, multiplication by
  `s` becomes multiplication by the function that represents `s` on `T`.
- `ChartOf` turns these identifications into module charts, `twistModChart`. Over each
  open `W ≤ T`, they are bijections on sections, compatible with restriction and with
  scalars. They are natural in `Z`.
- `Glue` proves `exists_global_lift`. Let `π` map one system of charted modules to
  another, surjectively on sections over affine opens. Let `p` be a family of global
  sections of the target system whose restriction to `U = trivializationOpen N s` lifts
  compatibly. Then some `p m` lifts to a global section. This is the lifting form of
  Stacks Lemma 28.18.2, tag [01PW](https://stacks.math.columbia.edu/tag/01PW).
- `Killing` proves `twistKilling` by induction on `p`, for all quasi-coherent `Z` at
  once. Choose an ordered affine cover `𝒰` of `X`. The Čech sequence
  `0 → Z → C⁰(𝒰, Z) → Q → 0` is short exact, and its middle term has vanishing higher
  cohomology because `X` is separated. All three terms are quasi-coherent. Twisting by
  `twistIter N k` keeps the sequence exact, and `twistPow N s k` is a morphism from the
  sequence to its twist. By naturality of the connecting map `δ`, a class `ξ = δ η` is
  killed once `twistPow N s k` sends `η ∈ Hᵖ(Q)` into the image of `Hᵖ(C⁰)`. For `p > 0`
  this holds by the induction hypothesis on `Q`. For `p = 0` it is a global lifting
  statement, which `exists_global_lift` provides.

### Step 2: from killing classes to the section-killing interface

The module `SerreVanishing.Adapter` proves this step. The kernel and cokernel hypotheses
make each map `H^i((G ⊗ N^(m+k)) ⊗ P) → H^i((G ⊗ N^(m+k+1)) ⊗ P)` surjective, by the
long exact sequences of `0 → ker → G → im → 0` and `0 → im → G ⊗ N → coker → 0` after
the exact twist. Comparison maps
`sequenceLift : (twistIter N k).obj ((G ⊗ N^m) ⊗ P) ⟶ (G ⊗ N^(m+k)) ⊗ P` are built
recursively from monoidal coherence maps. By `twistPow_sequenceLift`, multiplication by
`s ^ k` followed by this comparison is the composite of the first `k` transition maps.
So, by `twistKilling`, every class of `H^i((G ⊗ N^m) ⊗ P)` maps to zero after finitely
many transitions. Proper coherent cohomology is finite-dimensional over `K`, and all
transitions are surjective. So `finiteModule_surjective_sequence_eventually_isZero`
(module `SerreVanishing.FinitePropagation`) gives `t` with
`H^i((G ⊗ N^(m+t)) ⊗ P) = 0`.

### Step 3: dévissage

The module `SerreVanishing.Assembly` uses the published modules `SerreVanishing.Good`,
`SerreVanishing.Propagation`, `SerreVanishing.FinitePropagation`,
`SerreVanishing.Support`, `SerreVanishing.Devissage` and `SerreVanishing.Dimension`.
Properness makes `X` quasi-compact, locally noetherian and separated, and `Dimension`
bounds its topological Krull dimension by some `d`. `Devissage` proves, by induction on
the dimension of the support, that every coherent module is `Good`: one threshold for
both exponents makes all positive-degree cohomology of the twists vanish. Its successor
step uses the Library's integral-ideal filtration and sections with affine trivialization
locus (`Support`). The extension argument of `Propagation` and `FinitePropagation`
applies `SectionKillingStatement` along rays. With support bound `d + 1`, `Good` for `M`
is exactly the target conclusion.

## Modules of this contribution

New in this contribution, each with its own Markdown:

- `Langlands.AlgebraicGeometry.Modules.SerreVanishing.Mul`
- `Langlands.AlgebraicGeometry.Modules.SerreVanishing.Iterate`
- `Langlands.AlgebraicGeometry.Modules.SerreVanishing.Chart`
- `Langlands.AlgebraicGeometry.Modules.SerreVanishing.Glue`
- `Langlands.AlgebraicGeometry.Modules.SerreVanishing.ChartOf`
- `Langlands.AlgebraicGeometry.Modules.SerreVanishing.Killing`
- `Langlands.AlgebraicGeometry.Modules.SerreVanishing.Adapter`
- `Langlands.AlgebraicGeometry.Modules.SerreVanishing.Assembly`
- `Langlands.AlgebraicGeometry.Modules.ProperAmplePairSerreVanishingProof` (this module)

The modules `SerreVanishing.Twist`, `Good`, `Propagation`, `FinitePropagation`,
`Support`, `Devissage` and `Dimension` are already in the Library and are used
unchanged.

## Relation to the literature

The statement Markdown derives the two-bundle form from Stacks Lemma 30.16.1, tag
[0B5T](https://stacks.math.columbia.edu/tag/0B5T), and Lemma 30.17.4, tag
[01XR](https://stacks.math.columbia.edu/tag/01XR). The proof follows that derivation,
with two changes of route. The dévissage uses the Library's integral-ideal filtration
instead of associated points. Lemma 01XR is proved by dimension shifting through the
Čech sequence instead of through the colimit description of `H^p(X_s, F)` (tag
[09MR](https://stacks.math.columbia.edu/tag/09MR)).
