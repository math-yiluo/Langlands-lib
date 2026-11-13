# Langlands' combinatorial lemma for actual standard parabolics (Renard V.3.18): proof

Worker 5295 wrote this under Task 5295. The module
`Langlands.GroupScheme.Rational.LanglandsDecompositionProof` proves the published statement
`Langlands.GroupScheme.LanglandsCombinatorialDecompositionStatement` as the theorem
`Langlands.GroupScheme.langlandsCombinatorialDecomposition`, at an arbitrary universe `u`. This
is the target of Task 5923 (`cc6440ad-eb4c-4348-aab2-f17ec8d69907`), the proof successor of
Task 5474. The statement, its source (Renard 2026, V.3.18, printed pp.114–115 / PDF pp.120–121,
with the `μ⁻` cone of the V.5.5 proof) and its formal choices are documented in
`LanglandsDecompositionStatement.md` and `LanglandsDecompositionCones.md`. Neither those modules
nor anything they import is changed. The proof adds no hypothesis. Its axioms are `propext`,
`Classical.choice` and `Quot.sound`.

The proof follows the outline in the statement's "Why the statement is true", with two
changes. Uniqueness and the three projection characterizations are proved directly from
variational inequalities, so the generic Proposition of V.5.5 is not needed. The compatibility
with `P_∅` comes from uniqueness, so the inverse Gram matrix of `J` is never used. Only the
V.5.5 Corollary is used, for existence.

## Notation

`Δ = simpleRelativeRoots i ν`. For a character `α`, `α` also denotes `1 ⊗ α ∈ Vstar T`, and
`α̌ = D.coroot α`. `⟨y, α̌⟩` is `pair T y (1 ⊗ α̌)`. The real root span is
`relativeRootSpanReal i`, and `𝔞*_G` is the range of `rationalCharacterRestrictReal i`.
A decomposition `(K, μG, μp, μm)` of `μ` relative to `J` is a tuple with
`IsLanglandsDecomposition i ν D J μ K μG μp μm`.

## Declarations

All auxiliary declarations are in the namespace `Langlands.GroupScheme.LanglandsDecomposition`.

**The coroot formula and central directions.**

* `pair_coroot_mul_form_root`: `⟨y, α̌⟩ · B(α, α) = 2 B(y, α)` for every relative root `α`.
  It comes from the invariance of `B` under the class of `D.representative α`, which acts by
  `x ↦ x − ⟨x, α̌⟩ α` (the published `fullRealAction_representative`), and from `⟨α, α̌⟩ = 2`.
* `tmul_root_ne_zero` and `form_root_pos`: `α ≠ 0` and `B(α, α) > 0`.
* `form_self_nonneg` and `eq_zero_of_form_self_nonpos`: `B` is positive semidefinite, and
  `B(x, x) ≤ 0` forces `x = 0`.
* `pair_eq_zero_iff`, `pair_pos_iff` and `pair_nonneg_iff`: `⟨y, α̌⟩` and `B(y, α)` have the
  same sign. This follows from the coroot formula and `B(α, α) > 0`.
* `relativeWeylFullRealAction_restrictReal` and `pair_coroot_eq_zero_of_mem_range`: the Weyl
  group fixes `𝔞*_G` (the published `relativeWeylLatticeAction_torusCharacterRestrict`), so
  every element of `𝔞*_G` kills every coroot.
* `form_eq_zero_of_pair_eq_zero`: a vector that kills the coroots of a set `K` of roots is
  `B`-orthogonal to the real span of `K`.
* `form_eq_zero_of_mem_range_of_mem_rootSpan`: `𝔞*_G` is `B`-orthogonal to the root span.

**Cones of roots.**

* `form_nonneg_of_mem_hull`: if `⟨w, α̌⟩ ≥ 0` for all `α ∈ S`, then `B(z, w) ≥ 0` for every
  nonnegative combination `z` of `S`.
* `exists_split_of_mem_hull`: a nonnegative combination of `K` is a nonnegative combination of
  `K ∖ J` plus an element of the real span of `J`.
* `mem_span_of_mem_hull` and `span_le_rootSpan`: the obvious inclusions.

**Properties of an arbitrary decomposition** (section `Decomposition`, for any `J`). Let
`(K, μG, μp, μm)` be a decomposition of `μ` relative to `J`.

* `simple_subset_roots`: `Δ` consists of relative roots.
* `neg_m_mem_span` and `m_mem_rootSpan`: `−μm` lies in the real span of `K`, so `μm` lies in
  the root span.
* `form_p_m`, `form_G_p` and `form_G_m`: pairwise orthogonality. `μp` kills the coroots of `K`,
  and `μG` is central.
* `form_sub_G_central`: `μ − μG = μp + μm` is in the root span, hence `B`-orthogonal to `𝔞*_G`.
* `p_mem_closedFace`: `μp ∈ closedCorootFace i ν D J`, because `J ⊆ K`.
* `neg_m_mem_cone`: `−μm ∈ projectedRootNonnegCone i D J (Δ ∖ J)`, because `K ⊆ Δ`.
* `p_variational`: `B(μ − μp, w − μp) ≤ 0` for every `w` in `closedCorootFace i ν D J`. Here
  `μ − μp = μG + μm`. `μG` is orthogonal to `w − μp`, and `B(μm, μp) = 0`. Write
  `−μm = z + s` with `z` a nonnegative combination of `K ∖ J` and `s` in the span of `J`. Then
  `B(s, w) = 0` and `B(z, w) ≥ 0`, because `w` kills the coroots of `J` and pairs
  nonnegatively with the other simple coroots.
* `m_variational`: `B(μ − μm, w − μm) ≤ 0` for every `w` with
  `−w ∈ projectedRootNonnegCone i D J (Δ ∖ J)`. Here `μ − μm = μG + μp`, and
  `−w = z' + s'` as above. `μp` kills the coroots of `J ⊆ K` and pairs nonnegatively with
  every simple coroot.
* `nearest_of_variational`: `B(a − x, w − x) ≤ 0` implies
  `B(a − x, a − x) ≤ B(a − w, a − w)`.
* `eq_of_variational`: two points that satisfy the variational inequality against each other
  are equal. Adding the two inequalities gives `B(y − x, y − x) ≤ 0`.
* `eq_of_isLanglandsDecomposition`: two decompositions of `μ` relative to the same `J` agree.
  The `μp` agree and the `μm` agree by `eq_of_variational`, and then the `μG` agree because
  `μ = μG + μp + μm`. `K` is recovered from `μp` as the set of simple roots `α` with
  `⟨μp, α̌⟩ = 0`, since `⟨μp, α̌⟩ > 0` for simple `α ∉ K`.

**The V.5.5 Corollary for a positive definite form.**

* `exists_cone_decomposition_of_form`: let `E` be a real vector space with a symmetric
  positive definite bilinear form `β`, a basis `b` indexed by a finite type, and a family `ω`
  with `β(b i, ω j) = δ_ij`. Then every `x ∈ E` is `∑_{i ∉ F} tᵢ ωᵢ − ∑_{j ∈ F} sⱼ bⱼ` with
  `tᵢ > 0` and `sⱼ ≥ 0`. The proof builds an `InnerProductSpace.Core` from `β`, installs the
  induced normed and inner product space structures locally, and applies the published
  `Langlands.Renard.coneProjectionBasisStatement` (Task 5418). This module only uses the
  existence part of that corollary.

**Obtuseness and existence** (section `Existence`).

* `latticePairing_coroot_nonpos`: for distinct simple roots `α ≠ β`, `⟨α, β̌⟩ ≤ 0`. The
  published finite root pairing `D.rootPairing` on the rational root span is crystallographic.
  The simple roots lie in its base `IsAddIndecomposable.baseOf` for the functional `⟨·, ν⟩`;
  this is the argument of the published `linearIndepOn_simple_corootFunctional`. Mathlib's
  `RootPairing.baseOf_pairwise_pairing_le_zero` then gives the sign. Nonreduced systems are
  allowed.
* `pair_nonpos_of_mem_hull`: let `β` be a simple root outside `S ⊆ Δ`. Then every nonnegative
  combination of `S` pairs nonpositively with `β̌`.
* `isLanglandsDecomposition_of_empty`: suppose `J ⊆ Δ` and `μ ∈ corootAnnihilator i D J`.
  Then every decomposition of `μ` relative to `∅` is also a decomposition relative to `J`.
  Let `β ∈ J` with `β ∉ K`. Then `0 = ⟨μ, β̌⟩ = ⟨μp, β̌⟩ + ⟨μm, β̌⟩`, where the first term is
  positive and the second is nonnegative by `pair_nonpos_of_mem_hull`. This is impossible, so
  `J ⊆ K`. Then `−μm` kills the coroots of `J`, and `exists_split_of_mem_hull` gives the
  `K ∖ J` form of the cone condition.
* `exists_central_add_root`: `Vstar T = 𝔞*_G + root span`, from the published
  `relativeCharacterRootComplement`.
* `exists_dual_vector`: for each simple root `β` there is a `w` in the root span with
  `B(α, w) = δ_αβ` for every simple `α`. The published `exists_mem_openSimpleCorootFace`, for
  the set `Δ ∖ {β}`, gives `y` with `⟨y, α̌⟩ = 0` for simple `α ≠ β` and `⟨y, β̌⟩ > 0`. Its
  root-span component has the same coroot pairings. By the sign lemmas, a suitable multiple
  of it is the required `w`.
* `span_simple_eq_rootSpan`: the simple roots span the real root span. The published
  `relativeRoots_subset_addSubgroupClosure_simpleRelativeRoots` applies, with negation
  stability from `D.neg_mem_relativeRoots`.
* `exists_empty_decomposition`: every `μ ∈ Vstar T` has a decomposition relative to `∅`.
  Let `E` be the real root span. The simple roots form a basis `b` of `E`: they span by
  `span_simple_eq_rootSpan`, and they are linearly independent because `B(·, ω_β)` picks out
  the coefficient of `β`. The vectors `ω_β` from `exists_dual_vector` form the dual family.
  Write `μ = c + r` with `c ∈ 𝔞*_G` and `r ∈ E`, and apply `exists_cone_decomposition_of_form`
  to `r`. This gives `r = ∑_{i ∉ F} tᵢ ωᵢ − ∑_{j ∈ F} sⱼ αⱼ`. The tuple
  `(F, c, ∑_{i ∉ F} tᵢ ωᵢ, −∑_{j ∈ F} sⱼ αⱼ)` is a decomposition. The positive part `μp`
  satisfies `B(α_j, μp) = t_j > 0` for `j ∉ F` and `B(α_j, μp) = 0` for `j ∈ F`, so the
  sign lemmas place it in `openCorootFace i ν D F`. `−μm` is a nonnegative combination of `F`.

**The realization of `𝔞*_M`** (section `Realization`).

* `existsUnique_restrict` (conjunct 1). Take the compatible data `p, l, a, f` of `J`. The
  proved `standardLeviCentralDirections`, applied to `M` with the closed embedding `l ≫ p`,
  gives a morphism `f' : A → T`. It satisfies `f' ≫ i = a ≫ l ≫ p`, its real cocharacter map
  is injective, and its range is `rootAnnihilator T J`. Since `i` is a monomorphism and
  `f ≫ i = a ≫ l ≫ p`, we get `f' = f`. The published duality lemmas of
  `RealTorusDuality` then identify the kernel of restriction along `f` with the real span of
  `J`. Restriction is injective on `corootAnnihilator i D J`, because a vector in the span of
  `J` that kills the coroots of `J` has `B(x, x) = 0`. For surjectivity, count dimensions.
  `dim Vstar A = dim V A = dim rootAnnihilator T J = dim Vstar T − |J|`, by the perfect
  pairings `characterDualEquiv` and the published rank statement. `dim corootAnnihilator ≥
  dim Vstar T − |J|`, by rank–nullity for the map `y ↦ (⟨y, β̌⟩)_{β ∈ J}` to `ℝ^J`. So the
  injective restriction has equal dimensions on both sides and is bijective.

**Main theorem.**

* `langlandsCombinatorialDecomposition`. Conjunct 1 is `existsUnique_restrict`. Let
  `μ ∈ corootAnnihilator i D J`. `exists_empty_decomposition` gives a decomposition `d₀` of
  `μ` relative to `∅`. By `isLanglandsDecomposition_of_empty` it is also one relative to `J`,
  and by `eq_of_isLanglandsDecomposition` it is the only one. Let `d` be any decomposition
  relative to `J`. Then `d = d₀`. The orthogonality, the `𝔞*_G` projection and the two
  nearest-point properties come from the lemmas of section `Decomposition`, together with
  `nearest_of_variational`. For the compatibility with `P_∅`: a decomposition relative to `∅`
  equals `d₀` by uniqueness relative to `∅`, and `d = d₀` is one.

## Relation to the source

Renard proves V.3.18 in V.5.5 by applying the Euclidean Proposition and Corollary of V.5.5 to
`(𝔞^G_M)*` with the basis `Δ(P)` of projected roots. This proof applies the Corollary once, to
the full root span `(𝔞^G_∅)*` with the basis `Δ_∅`, which gives the decomposition relative to
`P_∅`. The obtuseness of simple roots then shows that this decomposition is also the
decomposition relative to `P` when `μ ∈ 𝔞*_M`. This route makes Renard's final remark (the
decomposition relative to `(μ, P_∅)` is the same) part of the existence proof. Uniqueness and
the projection properties use only the variational inequalities, which is the
characterization (ii) of the V.5.5 Proposition, proved here directly in `Vstar T`.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.GroupScheme.Rational.LanglandsDecompositionStatement` | the target statement and, through it, the cones and `IsLanglandsDecomposition` |
| `Langlands.GroupScheme.Rational.ParabolicWeylDisplacement` | `RelativeRootReflectionData.fullRealAction_representative` |
| `Langlands.GroupScheme.Rational.RelativeWeylFaithfulness` | `relativeWeylLatticeAction_torusCharacterRestrict` |
| `Langlands.GroupScheme.Rational.RelativeCharacterRootComplementProof` | `relativeCharacterRootComplement` |
| `Langlands.GroupScheme.Rational.StandardLeviCentralDirectionsProof` | `standardLeviCentralDirections` |
| `Langlands.GroupScheme.Rational.PositiveRootInduction` | `relativeRoots_subset_addSubgroupClosure_simpleRelativeRoots` |
| `Langlands.GroupScheme.Rational.ReflectionNegation` | `RelativeRootReflectionData.neg_mem_relativeRoots` |
| `Langlands.GroupScheme.Rational.RootSupportFiniteness` | `IsSplitTorus.finite_relativeRoots` |
| `Langlands.Geometry.Building.RealTorusDuality` | `characterDualEquiv`, `ker_restrictReal_eq_characterAnnihilator_range`, `rootAnnihilator_eq_cocharacterAnnihilator`, `characterAnnihilator_cocharacterAnnihilator` |
| `Langlands.Representation.LanglandsClassification.SimpleCorootFaceExistence` | `RelativeRootReflectionData.exists_mem_openSimpleCorootFace`, and through it `rootPairing` and `rootPairing_isCrystallographic` |
| `Langlands.Analysis.RenardConeProjectionProof` | `Langlands.Renard.coneProjectionBasisStatement` (V.5.5 Corollary) |
| `Mathlib.LinearAlgebra.RootSystem.BaseExists` | `RootPairing.baseOf_pairwise_pairing_le_zero` |
