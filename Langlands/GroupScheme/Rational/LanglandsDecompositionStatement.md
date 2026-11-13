# Langlands' combinatorial lemma for actual standard parabolics (Renard V.3.18): statement

Module `Langlands.GroupScheme.Rational.LanglandsDecompositionStatement`.
Namespace `Langlands.GroupScheme`. Universe parameter `u`.
The module contains one **statement**, the `Prop`-valued definition
`LanglandsCombinatorialDecompositionStatement`. It proves nothing. Worker 24 wrote it under
Task 5474 (`9abd0e5e-4606-4ee5-b449-49ac84438117`). The cones and the decomposition predicate
it uses are defined in `Langlands.GroupScheme.Rational.LanglandsDecompositionCones`. Their
Markdown gives the source passages V.3.7 and V.3.13–V.3.17, the realization of each cone, and
the source issue in the `μ⁻` cone.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026. It is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. V.3.18 is on printed
pp.114–115 / PDF pp.120–121. Worker 24 read it from rendered page images:

> **V.3.18 Lemme combinatoire de Langlands.** Soient `P = MN` un sous-groupe parabolique
> standard de `G` et `μ ∈ 𝔞*_M`. Le lemme combinatoire de Langlands affirme qu'il existe un
> unique sous-groupe parabolique standard `Q` contenant `P` tel que `μ` se décompose en
>
> (V.3.18.1) `μ = μ_G + μ⁺ + μ⁻`
>
> avec `μ_G ∈ 𝔞*_G`, `μ⁺ ∈ ^G_Q[(𝔞^G_L)*]^+` et `μ⁻ ∈ −p^L_M(⁺\overline{[𝔞*_M]}^G_P)`. Cette
> décomposition est unique. De plus `μ_G` est la projection orthogonale de `μ` sur `𝔞*_G`,
> `μ⁺` est la projection orthogonale de `μ` sur le cône `^G_P\overline{[(𝔞^G_M)*]}^+` et `μ⁻`
> est la projection orthogonale de `μ` sur le cône `⁻\overline{[𝔞*_M]}^G_P`. Les éléments
> `μ_G`, `μ⁺` et `μ⁻` sont deux à deux orthogonaux. Remarquons que si l'on considère `μ` comme
> un élément de `𝔞*_∅`, et que l'on applique le résultat ci-dessus à `(μ, P_∅)`, on trouve la
> même décomposition.

The in-book proof is V.5.5 (printed pp.127–129 / PDF pp.133–135). It applies the Euclidean
Proposition and Corollary of V.5.5 to `V = (𝔞^G_M)*` with basis `Δ(P)`. Those two results are
the published generic statement `Langlands.Renard.ConeProjectionStatements`, proved under Task
5418. Notation `⁻[𝔞]^G_P = −(⁺[𝔞]^G_P)` is from V.3.15.

Provenance: **source**, with one **derived** correction. The condition on `μ⁻` follows the V.5.5
proof (minus a nonnegative combination of the restricted roots of `K ∖ J`), not the literal
`−p^L_M(…)` of (V.3.18.1). Read literally, (V.3.18.1) does not determine `Q` (an `A_2`
counterexample is in the Markdown of `LanglandsDecompositionCones`). The three projection
characterizations, the orthogonality and the compatibility with `P_∅` are stated as in the
source.

## Bound objects

- `k` is any field, `G` a connected reductive group scheme over `k` (`IsConnectedReductive G`),
  and `i : T → G` a maximal split torus (`IsMaximalSplitTorus i`; Renard's `A_∅`). `ν` is a
  generic cocharacter (`IsGenericCocharacter i ν`). Its dynamic parabolic is the fixed minimal
  parabolic `P_∅`, and it fixes the simple relative roots `Δ_∅ = simpleRelativeRoots i ν`.
- `D : RelativeRootReflectionData i` supplies the coroots (see the Cones Markdown).
- `B : LinearMap.BilinForm ℝ (Vstar T)` with `IsWeylInvariantInnerProduct i B`: a symmetric,
  positive definite form on `𝔞*_∅ = Vstar T`, invariant under the actual relative Weyl group.
  This is the fixed inner product of V.3.7/V.3.13. Its restrictions to the subspaces `𝔞*_M`
  are the products used there.
- `A`, `P`, `M`, `p : P → G`, `l : M → P`, `a : A → M`, `J`, `f : A → T` must satisfy
  `ParabolicRootPresentationData.IsCompatible` for `⟨T, i, ν, J, f⟩`. That is the published
  all-test compatibility of actual data: `p` is a parabolic subgroup whose image is
  `standardParabolic i ν J`, `l` is a rational Levi subgroup whose image (through `p`) is
  `standardLevi i ν J`, `a` is the split component of `M` (Renard's `A_M`),
  `J ⊆ simpleRelativeRoots i ν` (Renard's `Δ^M_∅`), the minimal parabolic of `ν` is contained
  in `P`, and `f ≫ i = a ≫ l ≫ p` (the inclusion `A_M ⊂ A_∅`). So `P = MN` is an actual
  standard parabolic with its standard Levi factor.
- `Vstar A = ℝ ⊗_ℤ X*(A)` is the actual real character space of `A_M`. By V.3.6 this is
  Renard's `𝔞*_M = X*(M) ⊗ ℝ ≅ X*(A_M) ⊗ ℝ`.

## The statement

`LanglandsCombinatorialDecompositionStatement` asserts, for all the bound objects above:

1. **The realization of `𝔞*_M` in `𝔞*_∅`.** For every `x ∈ Vstar A` there is a unique
   `y ∈ corootAnnihilator i D J` whose restriction along `f`
   (`rationalCharacterRestrictReal (groupHom f)`) is `x`. In other words, restriction is a
   bijection from Renard's `𝔞*_M ⊂ 𝔞*_∅` (V.3.13, annihilator of the coroots of `M`) onto the
   actual `X*(A_M) ⊗ ℝ`.
2. For every `μ ∈ corootAnnihilator i D J` (that is, every `μ ∈ 𝔞*_M`):
   1. **Existence and uniqueness.** There is exactly one tuple `(K, μG, μp, μm)` with
      `IsLanglandsDecomposition i ν D J μ K μG μp μm`. In that tuple `J ⊆ K ⊆ Δ_∅` (`Q ⊇ P`),
      `μ = μG + μp + μm`, `μG ∈ 𝔞*_G`, `μp ∈ ^G_Q[(𝔞^G_L)*]^+` and `−μm` lies in the closed cone
      of restricted roots of `K ∖ J`.
   2. For every tuple satisfying `IsLanglandsDecomposition i ν D J μ K μG μp μm`:
      - **`μ_G` is the orthogonal projection on `𝔞*_G`:** `B (μ − μG) z = 0` for every
        `z ∈ (rationalCharacterRestrictReal i).range`. Together with `μG ∈ 𝔞*_G`, this
        characterizes the orthogonal projection.
      - **`μ⁺` is the projection on the closed cone `^G_P\overline{[(𝔞^G_M)*]}^+`:**
        `μp ∈ closedCorootFace i ν D J` and `B (μ − μp) (μ − μp) ≤ B (μ − w) (μ − w)` for every
        `w` in that cone.
      - **`μ⁻` is the projection on the closed cone `⁻\overline{[𝔞*_M]}^G_P`:**
        `−μm ∈ projectedRootNonnegCone i D J (Δ_∅ ∖ J)` and
        `B (μ − μm) (μ − μm) ≤ B (μ − w) (μ − w)` for every `w` with
        `−w ∈ projectedRootNonnegCone i D J (Δ_∅ ∖ J)`.
      - **Pairwise orthogonality:** `B μG μp = 0`, `B μG μm = 0`, `B μp μm = 0`.
      - **Compatibility with `(μ, P_∅)`:** for every `(K', μG', μp', μm')`,
        `IsLanglandsDecomposition i ν D ∅ μ K' μG' μp' μm'` holds exactly when
        `(K', μG', μp', μm') = (K, μG, μp, μm)`. Viewing `μ` in `𝔞*_∅` and decomposing with
        respect to `P_∅` (`J = ∅`) gives the same `Q` and the same three components.

## Correspondence with the source

| Renard | Lean |
| --- | --- |
| `G`, `A_∅`, `P_∅` | `G`, `i : T → G` maximal split, generic `ν` |
| standard `P = MN`, `A_M` | actual `p`, `l`, `a` with `IsCompatible` for `J` |
| `𝔞*_M` (V.3.6) and its realization in `𝔞*_∅` (V.3.13) | `Vstar A`, `corootAnnihilator i D J`, conjunct 1 |
| fixed `W`-invariant inner product (V.3.7, V.3.13) | `B` with `IsWeylInvariantInnerProduct i B` |
| standard `Q = LU ⊇ P` | `K` with `J ⊆ K ⊆ Δ_∅`, `Q = standardParabolic i ν K`, `L = standardLevi i ν K` |
| `𝔞*_G` | `(rationalCharacterRestrictReal i).range` |
| `^G_Q[(𝔞^G_L)*]^+` | `openCorootFace i ν D K` |
| `^G_P\overline{[(𝔞^G_M)*]}^+` | `closedCorootFace i ν D J` |
| `⁺\overline{[𝔞*_M]}^G_P` | `projectedRootNonnegCone i D J (Δ_∅ ∖ J)` |
| `μ⁻ ∈ −p^L_M(⁺\overline{[𝔞*_M]}^G_P)` | `−μm ∈ projectedRootNonnegCone i D J (K ∖ J)` (corrected) |
| projection on a closed cone (V.5.5 (i)) | nearest point for `B` |
| `(μ, P_∅)` | `IsLanglandsDecomposition i ν D ∅ μ …` |

## Formal choices

- **Where `μ` lives.** Renard decomposes inside `𝔞*_M`, using its V.3.13 realization in
  `𝔞*_∅` and the restricted inner product. The statement does the same: `μ` and its components
  are vectors of `Vstar T` in `corootAnnihilator i D J`. Conjunct 1 then states, as a
  conclusion, that this subspace is identified with the actual `Vstar A` by restriction along
  the actual `f`. So "every `μ ∈ 𝔞*_M`" is equivalent to "every `x ∈ Vstar A`, through its
  unique lift". No identification, inner product or compatibility on `Vstar A` is supplied as
  input.
- **`Q` as a set of simple roots.** The unique standard parabolic `Q ⊇ P` is encoded by
  `K ⊆ Δ_∅` with `J ⊆ K`. By the published `StandardParabolicOrderStatement`,
  `K ↦ standardParabolic i ν K` is injective on subsets of `Δ_∅`, and `P ⊆ Q` iff `J ⊆ K`.
  So uniqueness of `K` is uniqueness of `Q`. Uniqueness of the whole tuple covers both "unique
  `Q`" and "Cette décomposition est unique".
- **`𝔞*_G` with full central directions.** `𝔞*_G` is the image of the actual real rational
  characters of `G`. No finite-dimensionality, splitness of the center or rank hypothesis is
  added.
- **Projections.** "Projection orthogonale sur le cône" is stated as the nearest-point
  property (i) of the V.5.5 Proposition for the norm of `B`. The orthogonal projection on the
  subspace `𝔞*_G` is stated as `μG ∈ 𝔞*_G` with `μ − μG ⊥ 𝔞*_G`. All three are projections of
  `μ` itself, as in the source. Projecting `μ − μ_G` gives the same points, because `𝔞*_G` is
  orthogonal to the root span.
- **Corrected `μ⁻` condition.** See "Source and provenance" and the Cones Markdown. The
  characterization of `μ⁻` as the projection on `⁻\overline{[𝔞*_M]}^G_P` uses the source's
  `G`-cone unchanged.
- **Ground field.** Any field. Renard works over a nonarchimedean local field, but the lemma is
  about the relative root datum.
- **Hypotheses.** Only structural data are quantified: `D` (integral reflection data: pairing
  2 and the reflection formula realized by actual normalizer points) and `B` (symmetric,
  positive definite, Weyl invariant). Nothing about the decomposition, its uniqueness, the
  projections, or the identification of `𝔞*_M` is assumed.

## Why the statement is true

The following facts are the inputs.

- `Vstar T = 𝔞*_G ⊕ (𝔞^G_∅)*` (proved `RelativeCharacterRootComplementStatement`). The
  characters of `G` are Weyl-fixed, so for invariant `B` they are orthogonal to every root
  (`B(χ, α) = B(s_α χ, s_α α) = −B(χ, α)`) and kill every coroot.
- `Δ_∅` is a basis of the root span (`RelativeSimpleRootBasisStatement`).
- `⟨x, α̌⟩ = 2B(x, α)/B(α, α)`, by `D.action` and the invariance of `B`.

Then `𝔞*_M = 𝔞*_G ⊕ (𝔞^G_M)*`, where `(𝔞^G_M)*` is the root span intersected with the
`B`-orthogonal of `span(J)`. Inside it, the vectors `p_M(α)`, `α ∈ Δ_∅ ∖ J`, form a basis `Δ(P)`.
`closedCorootFace J` is the dual cone `{y : B(y, p_M α) ≥ 0}`, and its polar is
`−projectedRootNonnegCone J (Δ_∅ ∖ J)`.

The V.5.5 Corollary (Moreau decomposition) in `(𝔞^G_M)*` writes `μ − μ_G` uniquely as
`Σ_{i ∉ F} t_i ω_i − Σ_{j ∈ F} s_j α_j` with `t > 0`, `s ≥ 0`. The set `K = J ∪ F` gives `Q`,
`μ⁺` and `μ⁻`. Uniqueness: any tuple has `μG` equal to the `𝔞*_G`-component of `μ`. Its `μp`
and `μm` are in the closed cone and its polar, and they are orthogonal, since `μp` kills the
roots of `K` and `μm` is a combination of them. So they are the two projections, and `K` is
recovered as the simple roots `α` with `⟨μp, α̌⟩ = 0`.

Compatibility with `P_∅`: for `α ∉ J` simple, `p_M(α) = α − Σ_{β ∈ J} c_β β` with `c ≤ 0`. The
reason is that `B(α, β) ≤ 0` for distinct simple roots and the inverse Gram matrix of `J` is
entrywise nonnegative. So `−μm` is a nonnegative combination of the roots in `K`, and the
tuple is also a `J = ∅` decomposition, which is unique.

## Remaining proof obligations

The proof is a separate obligation (an exact proof successor task will name
`Langlands.GroupScheme.LanglandsCombinatorialDecompositionStatement`). The prerequisites below
are not established by this module. They are recorded here so that they are not mistaken for
proved structural results:

1. The real form of the simple-root basis of the relative root span, and the sign property of
   root coefficients (from `RelativeSimpleRootBasisStatement` and `HasRelativeRootSystem`).
2. The coroot formula `⟨x, α̌⟩ = 2B(x, α)/B(α, α)`, from `D.action` and the Weyl invariance of
   `B`. Real characters of `G` restricted to `T` kill all coroots and are `B`-orthogonal to the
   root span.
3. `B(α, β) ≤ 0` for distinct simple roots, and entrywise nonnegativity of the inverse Gram
   matrix of any set of simple roots.
4. The identification of conjunct 1: the kernel of restriction along `f` is `span_ℝ(J)` (the
   dual form of `StandardLeviSplitCentralDirectionsStatement`, whose `f` agrees with the given
   one because `i` is a monomorphism), and `corootAnnihilator i D J` is a complement of
   `span_ℝ(J)`.
5. The generic V.5.5 Proposition and Corollary (`Langlands.Renard.ConeProjectionStatements`),
   applied to `(𝔞^G_M)*` with the restricted inner product.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.GroupScheme.Rational.LanglandsDecompositionCones` | `corootAnnihilator`, `closedCorootFace`, `projectedRootNonnegCone`, `IsWeylInvariantInnerProduct`, `IsLanglandsDecomposition`, and through them `Vstar`, `rationalCharacterRestrictReal`, `RelativeRootReflectionData`, `simpleRelativeRoots` |
| `Langlands.GroupScheme.Rational.ParabolicRootPresentation` | `ParabolicRootPresentationData`, `IsCompatible`, and through it `IsConnectedReductive`, `IsMaximalSplitTorus`, `IsGenericCocharacter`, `CommGroupScheme.groupHom` |
