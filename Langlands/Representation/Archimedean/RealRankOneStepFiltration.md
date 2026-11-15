# The rank-one step from filtrations of standard modules

Worker 32 wrote this module for Task 6747 (`505270a8-39b1-487d-afdb-01f552e4ab3b`). That task's
target is the Library's `Langlands.Archimedean.RealLanglandsFromPrincipalSeriesStatement`.
Worker 63's module `RealLanglandsRankOneReduction` reduces the target to one statement,
`RealRankOneStepStatement` (see `RealLanglandsRankOneReduction.md`). This module reduces that
statement to two statements about standard modules alone, with no target module `(ρ, π)`:

- `RealCharacterPairFiltrationStatement`, for two adjacent character blocks (a statement about
  `GL₂(ℝ)`, induced in stages);
- `RealInducedPairFiltrationStatement`, for two adjacent blocks of which at least one is an
  induction block (a statement about `GL₃(ℝ)` or `GL₄(ℝ)`, induced in stages).

It proves that the two imply `RealRankOneStepStatement` (`realRankOneStep_of_filtration`).
That proof uses neither irreducibility nor admissibility of `(ρ, π)`.

All declarations are in the namespace `Langlands.Archimedean`. The Library's `RealBlock`,
`realRank`, `RealCharacterData` and `ComplexCharacterData` are in
`Langlands.LocalFactor.Archimedean`. `kFiniteFunctions`, `rightDerivative` and
`realStandardModule` are in `StandardModule.lean`. `realBlockExponent` and
`IsRealStandardIntertwiner` are in `RealGenericParameterReduction.lean`. `realExponentSupport`,
`realWeightSquareSum` and `RealRankOneStepStatement` are in `RealLanglandsRankOneReduction.lean`.

Notation: `S(ds)` is `kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)`, the
`O(n)`-finite functions of the standard module of the list of real blocks `ds`. `R(k)` is right
translation by `k ∈ O(n)` (`Whittaker.rightTranslation`). `R(X)` is the right derivative along
`X ∈ 𝔤𝔩_n(ℝ)` (`rightDerivative (matrixModel ℝ n) X`).

## Definitions

### `IsRealIntertwinerModulo n ds es M q`

Data: `n : ℕ`, lists `ds es : List RealBlock`, a subspace `M : Submodule ℂ S(es)` and a
`ℂ`-linear map `q : S(ds) →ₗ[ℂ] S(es)`. The proposition is the conjunction of:

- for every `k : unitaryCompact ℝ n` and `f : S(ds)`, there are proofs `hf` that `R(k) f` lies
  in `S(ds)` and `hg` that `R(k) (q f)` lies in `S(es)`, such that
  `q ⟨R(k) f, hf⟩ - ⟨R(k) (q f), hg⟩ ∈ M`;
- for every `X : Matrix (Fin n) (Fin n) ℝ` and `f : S(ds)`, there are proofs `hf` that
  `R(X) f` lies in `S(ds)` and `hg` that `R(X) (q f)` lies in `S(es)`, such that
  `q ⟨R(X) f, hf⟩ - ⟨R(X) (q f), hg⟩ ∈ M`.

So `q` is a `(𝔤, K)`-intertwiner modulo `M`. If `M` is a `(𝔤, K)`-submodule, this says that
`q` followed by the projection `S(es) → S(es)/M` is a `(𝔤, K)`-intertwiner. The membership
proofs are existentially quantified, as in `IsRealStandardIntertwiner`.

Provenance: internal. It is the definition of `IsRealStandardIntertwiner` with the equation
weakened to a congruence modulo `M`, for maps between two standard modules.

### `RealAdjacentFiltration n pre post x y`

Data: `n : ℕ`, lists `pre post : List RealBlock` and blocks `x y : RealBlock`. The proposition
says that there are

- a number `k : ℕ`;
- lists of real blocks `ws : Fin k → List RealBlock`;
- linear maps `q j : S(pre ++ ws j ++ post) →ₗ[ℂ] S(pre ++ x :: y :: post)`, for `j : Fin k`,

such that

1. for every `j`, either `ws j = [y, x]`, or both
   `(realExponentSupport (ws j)).Perm (realExponentSupport [x, y])` and
   `realWeightSquareSum [x, y] < realWeightSquareSum (ws j)`;
2. for every `j`, `IsRealIntertwinerModulo n (pre ++ ws j ++ post) (pre ++ x :: y :: post)
   (⨆ (i : Fin k) (_ : i < j), LinearMap.range (q i)) (q j)`: the map `q j` is an intertwiner
   modulo the span of the ranges of the earlier maps;
3. `⨆ j, LinearMap.range (q j) = ⊤`: the ranges of all the maps span `S(pre ++ x :: y :: post)`.

Meaning. Let `F_j` be the span of the ranges of `q i` for `i < j`. By induction on `j`, using
2, each `F_j` is a `(𝔤, K)`-submodule; `F_0 = 0`, and `F_k` is everything by 3. The map `q j`
followed by the projection to `F_(j+1)/F_j` is a surjective `(𝔤, K)`-intertwiner. So every
graded piece `F_(j+1)/F_j` is a quotient of the standard module of `pre ++ ws j ++ post`, and
`q j` is a linear lift of the quotient map. Condition 1 lists the allowed lists `ws j`. They
are the two alternatives of `RealRankOneStepStatement`: the exchanged pair, or a list with the
same exponent support up to order and a strictly larger sum of squared weights. The Lean
definition does not state this paragraph; it only states 1–3.

Provenance: internal. It packages a filtration of a standard module with prescribed quotients
of standard modules as graded pieces, in a form that needs no quotient modules.

## Statements

### `RealCharacterPairFiltrationStatement`

For every `n : ℕ`, `pre post : List RealBlock` and `c d : RealCharacterData`, if

- `realRank (pre ++ .character c :: .character d :: post) = n`, and
- `realBlockExponent (.character c) < realBlockExponent (.character d)`, that is,
  `Re c.exponent < Re d.exponent`,

then `RealAdjacentFiltration n pre post (.character c) (.character d)`.

### `RealInducedPairFiltrationStatement`

For every `n : ℕ`, `pre post : List RealBlock` and `x y : RealBlock`, if

- `x = .induced e` for some `e`, or `y = .induced e` for some `e`;
- `realRank (pre ++ x :: y :: post) = n`;
- `realBlockExponent x < realBlockExponent y`,

then `RealAdjacentFiltration n pre post x y`.

The two statements cover all adjacent pairs; together they say that every pair
`pre ++ x :: y :: post` of total rank `n` with `Re t(x) < Re t(y)` has such a filtration. The
split separates the `GL₂(ℝ)` case, where the composition series is explicit (example below),
from the cases that need the composition series of `GL₃(ℝ)` and `GL₄(ℝ)` standard modules.

### Why the statements should hold

Provenance: derived. Neither statement is in the literature in this form. They follow from the
composition-series argument of `RealLanglandsRankOneReduction.md` (section
`RealRankOneStepStatement`, steps 1–6), run for every composition factor instead of the one
that maps to `(ρ, π)`. That argument is not in the cited texts either. It combines Knapp–Vogan
1995 (`knapp-vogan-1995-cohomological-induction`) (11.196) and Theorem 11.198(c) with Remark 4
after it (printed pp. 740–742, PDF pp. 762–764), Knapp 1994 (`knapp-1994-archimedean-llc`)
Theorem 1 (printed p. 400, PDF p. 410), and standard facts named there. They are not checked on
a page here. In outline, with `r = rank x + rank y` and the notation `I(ws)`, `σ_pre`, `σ_post`,
`Ind(σ_pre ⊗ W ⊗ σ_post)` of that Markdown:

1. Let `0 = G₀ ⊂ ⋯ ⊂ G_k = I(x, y)` be a composition series of the `GL_r(ℝ)` standard module
   of `[x, y]`, which has finite length. By that Markdown's steps 2, 3 and 6, every factor
   `τ_j = G_(j+1)/G_j` is either `J(y, x)`, the unique irreducible quotient of `I(y, x)`, or a
   quotient `J(zs)` of `I(zs)` for a list `zs` with exponent support a permutation of that of
   `[x, y]` and a strictly larger sum of squared weights. Put `ws j = [y, x]` in the first case
   and `ws j = zs` in the second. Condition 1 holds.
2. By exactness of parabolic induction and induction in stages (that Markdown's step 1), the
   modules `Ind(σ_pre ⊗ G_j ⊗ σ_post)` filter the standard module of `pre ++ x :: y :: post`.
   The `j`-th graded piece `Ind(σ_pre ⊗ τ_j ⊗ σ_post)` is a quotient of
   `Ind(σ_pre ⊗ I(ws j) ⊗ σ_post)`, the standard module of `pre ++ ws j ++ post`. Taking
   `O(n)`-finite vectors is exact on admissible representations, so the same holds for the
   `O(n)`-finite parts.
3. Let `q j` be a `ℂ`-linear lift of the surjection from `S(pre ++ ws j ++ post)` onto the
   `O(n)`-finite part of the `j`-th graded piece, with values in the `O(n)`-finite part of
   `Ind(σ_pre ⊗ G_(j+1) ⊗ σ_post)`. A lift exists since vector spaces are free. By induction on
   `j`, the span of the ranges of `q i`, `i < j`, is the `O(n)`-finite part of
   `Ind(σ_pre ⊗ G_j ⊗ σ_post)`. This gives conditions 2 and 3.

As for `RealRankOneStepStatement`, a proof must also identify the Library's
`realStandardModule` and its `(𝔤, K)`-action with the classical standard modules.

Example: two characters on `GL₂(ℝ)` (`pre = post = []`). Let `x = sgn^ε₁ |·|^{s₁}` and
`y = sgn^ε₂ |·|^{s₂}` with `Re s₁ < Re s₂`. The following description is standard and not
checked on a page here.

- If `Ind(x ⊗ y)` is irreducible, the standard intertwining operator from `Ind(y ⊗ x)`, given
  by a convergent integral since `Re s₂ > Re s₁`, is an isomorphism onto `Ind(x ⊗ y)`. Then
  `k = 1`, `ws 0 = [y, x]` and `q 0` is that operator.
- Otherwise `s₂ - s₁ = ℓ` is a positive integer of the right parity. Then `Ind(x ⊗ y)` has a
  finite-dimensional subrepresentation `F`, the image of the same operator. That image is the
  Langlands quotient of `Ind(y ⊗ x)` (Knapp 1994, p. 400, the remark after Theorem 1). The
  quotient by `F` is the discrete series `D_ℓ ⊗ |det|^t` with `t = (s₁ + s₂)/2`. Then `k = 2`,
  `ws 0 = [y, x]` with `q 0` that operator, and `ws 1 = [.induced e]`, where `e` has weight
  `±ℓ` and exponent `t`. Its exponent support is `[t + ℓ/2, t - ℓ/2]`, a permutation of
  `[s₁, s₂]`, and its squared weight is `ℓ² > 0`. The map `q 1` is a linear lift of the
  isomorphism from the standard module `D_ℓ ⊗ |det|^t` of `[.induced e]` onto `Ind(x ⊗ y)/F`.

### `RealRankOneStepFromFiltrationStatement.{uV}`

`RealCharacterPairFiltrationStatement → RealInducedPairFiltrationStatement →
RealRankOneStepStatement.{uV}`.

Provenance: internal; the reduction is proved in this module.

## Lemmas

- `IsRealIntertwinerModulo.comp hq hB hM`. Let `q : S(ds) →ₗ[ℂ] S(es)` satisfy
  `IsRealIntertwinerModulo n ds es M q`. Let `B : S(es) →ₗ[ℂ] V` satisfy
  `IsRealStandardIntertwiner n ρ π es B` and `M ≤ LinearMap.ker B`. Then
  `IsRealStandardIntertwiner n ρ π ds (B ∘ₗ q)`. Proof, for `k` (the case of `X` is the same):
  - `hq` gives `hf`, `hg` and `q ⟨R(k) f, hf⟩ - ⟨R(k) (q f), hg⟩ ∈ M`.
  - `B` kills this difference, so `B (q ⟨R(k) f, hf⟩) = B ⟨R(k) (q f), hg⟩`.
  - `hB` applied to `q f` gives `B ⟨R(k) (q f), hg'⟩ = ρ(k) (B (q f))`. The two subtype elements
    are equal by proof irrelevance, and `simpa` finishes with witness `hf`.
- `realAdjacentFiltration_of_statements hC hI n pre post x y hrank hxy`: both filtration
  statements give `RealAdjacentFiltration n pre post x y` for every pair. Proof by cases on
  `x` and `y`: two characters use `hC`; otherwise `hI` applies, with `⟨_, rfl⟩` for the
  induction block.
- `realRankOneStep_conclusion_of_mem hws B hB0 hB`. Let `ws` be a list allowed by condition 1,
  and `B` a nonzero intertwiner from `S(pre ++ ws ++ post)`. Then the conclusion of
  `RealRankOneStepStatement` holds. Proof by cases on `hws`:
  - If `ws = [y, x]` (substituted by `rcases … rfl`), rewrite
    `pre ++ [y, x] ++ post = pre ++ y :: x :: post` (`simp`) in the existential; this is the
    first alternative.
  - Otherwise `zs = ws` gives the second alternative.

## The reduction: `realRankOneStep_of_filtration`

It proves `RealRankOneStepFromFiltrationStatement.{uV}`. Take the data of
`RealRankOneStepStatement`: a nonzero intertwiner `B` from `S(pre ++ x :: y :: post)` with
`Re t(x) < Re t(y)` and total rank `n`. The hypotheses that `(ρ, π)` is a `(𝔤, K)`-module, is
irreducible and is admissible are not used.

1. `realAdjacentFiltration_of_statements` gives `k`, `ws`, `q` with conditions 1–3.
2. Some `j` has `B ∘ₗ q j ≠ 0`. Otherwise every range lies in `ker B`
   (`LinearMap.range_le_ker_iff`), so `⊤ = ⨆ j, range (q j) ≤ ker B` (`iSup_le`), and
   `B = 0` (`LinearMap.ker_eq_top`), a contradiction.
3. Let `j` be the least such index (`WellFounded.min wellFounded_lt` on `Fin k`, with
   `WellFounded.min_mem`). For `i < j`, `B ∘ₗ q i = 0` (`WellFounded.not_lt_min`). So the span
   of the earlier ranges lies in `ker B` (`iSup_le`, twice).
4. `IsRealIntertwinerModulo.comp` shows that `B ∘ₗ q j` is an intertwiner from
   `S(pre ++ ws j ++ post)`. It is nonzero by the choice of `j`, and
   `realRankOneStep_conclusion_of_mem` gives the conclusion.

The proof uses only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
