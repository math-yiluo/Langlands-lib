# The induced-pair filtration from `GL₃(ℝ)`, `GL₄(ℝ)` and induction in stages

The target of this module is the Library's `Langlands.Archimedean.RealInducedPairFiltrationStatement` (module
`RealRankOneStepFiltration`, see `RealRankOneStepFiltration.md`). This module splits the target
into four statements and proves that they imply it (`realInducedPairFiltration_of_base`):

- `RealAdjacentFiltrationInStagesStatement`: induction in stages. A filtration of the
  standard module of the pair `[x, y]` alone, on `GL_r(ℝ)` with `r = realRank [x, y]`, gives
  one of the standard module of `pre ++ x :: y :: post` on `GL_n(ℝ)`.
- Three base cases with `pre = post = []`:
  - `RealCharacterInducedFiltrationStatement` (`GL₃(ℝ)`, character then induction block);
  - `RealInducedCharacterFiltrationStatement` (`GL₃(ℝ)`, induction block then character);
  - `RealInducedInducedFiltrationStatement` (`GL₄(ℝ)`, two induction blocks).

All declarations are in the namespace `Langlands.Archimedean`. The Library's `RealBlock`,
`realRank`, `RealCharacterData` and `ComplexCharacterData` are in
`Langlands.LocalFactor.Archimedean`. `realBlockExponent` is in
`RealGenericParameterReduction.lean`. `RealAdjacentFiltration` and
`RealInducedPairFiltrationStatement` are in `RealRankOneStepFiltration.lean`.

Notation: `S(ds)` is `kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)`, the
`O(n)`-finite functions of the standard module of the list of real blocks `ds`, as in
`RealRankOneStepFiltration.md`. The rank of a character block is `1` and that of an induction
block is `2`, so `realRank [x, y]` is `2`, `3` or `4`.

## Statements

### `RealAdjacentFiltrationInStagesStatement`

For every `n : ℕ`, `pre post : List RealBlock` and `x y : RealBlock`, if

- `realRank (pre ++ x :: y :: post) = n`, and
- `RealAdjacentFiltration (realRank [x, y]) [] [] x y`,

then `RealAdjacentFiltration n pre post x y`.

No condition on the exponents of `x` and `y` and no condition on the kind of blocks is assumed.
In words: a filtration of `S([x, y])` on `GL_r(ℝ)`, `r = realRank [x, y]`, whose graded pieces
are quotients of `S(ws j)` with `ws j` allowed by condition 1 of `RealAdjacentFiltration`,
gives a filtration of `S(pre ++ x :: y :: post)` on `GL_n(ℝ)` whose graded pieces are
quotients of `S(pre ++ ws j ++ post)`, with the same lists `ws j`.

Provenance: derived. It is the `(𝔤, K)`-module form of exactness of parabolic induction
together with induction in stages, for the standard parabolic subgroup of `GL_n(ℝ)` with blocks
of sizes `realRank pre`, `r`, `realRank post`. These are the facts used in step 2 of
"Why the statements should hold" in `RealRankOneStepFiltration.md` and in step 1 of the
argument for `RealRankOneStepStatement` in `RealLanglandsRankOneReduction.md`. Induction in
stages is Knapp–Vogan 1995 (`knapp-vogan-1995-cohomological-induction`) formula (11.196),
printed p. 740, PDF p. 762: a standard continuous-series representation induced from the
parabolic subgroup `MAN` equals the representation induced in stages, first from the parabolic
subgroup `M''A''N''` of a larger Levi factor `M'` to `M'`, then from `M'A'N'` to `G`, the map
being `F ↦ F(·)(1)` (see also `StandardModule.md`, item 1). Exactness of
parabolic induction, which turns a filtration of the inner module into one of the outer module
with the same graded pieces, is not checked on a page here. Condition 1 of
`RealAdjacentFiltration` refers only to `x`, `y` and `ws j`, so it carries over unchanged.

### `RealCharacterInducedFiltrationStatement`

For every `c : RealCharacterData` and `d : ComplexCharacterData`, if
`realBlockExponent (.character c) < realBlockExponent (.induced d)`, that is,
`Re c.exponent < Re d.exponent`, then
`RealAdjacentFiltration 3 [] [] (.character c) (.induced d)`.

### `RealInducedCharacterFiltrationStatement`

For every `d : ComplexCharacterData` and `c : RealCharacterData`, if
`realBlockExponent (.induced d) < realBlockExponent (.character c)`, that is,
`Re d.exponent < Re c.exponent`, then
`RealAdjacentFiltration 3 [] [] (.induced d) (.character c)`.

### `RealInducedInducedFiltrationStatement`

For every `d e : ComplexCharacterData`, if
`realBlockExponent (.induced d) < realBlockExponent (.induced e)`, that is,
`Re d.exponent < Re e.exponent`, then
`RealAdjacentFiltration 4 [] [] (.induced d) (.induced e)`.

Provenance of the three base statements: internal. Each is the special case
`pre = post = []` of `RealInducedPairFiltrationStatement` for one of the three kinds of
pairs with an induction block; `realRank [x, y]` is `3` or `4` for these pairs. Weight-zero
induction blocks are included.

### Why the base statements should hold, and what a proof cannot use

The truth argument is step 1 of "Why the statements should hold" in
`RealRankOneStepFiltration.md`. It uses, for `GL₃(ℝ)` and `GL₄(ℝ)`:

- the existence half of the Langlands classification, Knapp 1994 (`knapp-1994-archimedean-llc`)
  Theorem 1 (printed p. 400, PDF p. 410), to write every composition factor as the Langlands
  quotient of a standard module;
- Knapp–Vogan 1995 (`knapp-vogan-1995-cohomological-induction`) Theorem 11.198(c) with Remark 4
  after it (printed pp. 740–742, PDF pp. 762–764), for `|Re ν'| < |Re ν|`;
- finite length of standard modules and linear independence of the distribution characters of
  irreducible representations (Harish-Chandra).

The classification for `GL₃(ℝ)` and `GL₄(ℝ)` is the case
`n = 3, 4` of `RealLanglandsFromPrincipalSeriesStatement`. The proof of that statement (module
`RealLanglandsFromPrincipalSeriesProof`) uses the present statements, so a proof of a base
statement cannot go through it. It has to describe the composition series explicitly (for example by a Speh–Vogan-type
analysis of `O(3)`- and `O(4)`-types and block intertwining operators) or take another
independent route.

Remarks for a proof. They are not checked on a page here and are not part of any statement.

- Condition 1 of `RealAdjacentFiltration` is the Langlands-lemma inequality of Remark 4: for a
  fixed exponent support, a strictly larger `realWeightSquareSum` is the same as a strictly
  smaller `|Re ν|`, by the trace-form identity
  `|Re ν(ds)|² = Σ_{s ∈ realExponentSupport ds} (Re s)² - realWeightSquareSum ds / 2`
  explained in `RealLanglandsRankOneReduction.md`. Real parts are essential here, since the
  exponents are complex: an induction block of weight `m` and exponent `t` contributes
  `(Re t + |m|/2)² + (Re t - |m|/2)² = 2 (Re t)² + m²/2` to the first sum and `2 (Re t)²` to
  the left side.
- The mirror case `[D, χ]` of `[χ, D]` on `GL₃(ℝ)` could be derived through the
  outer automorphism `g ↦ w₀ (gᵀ)⁻¹ w₀`, which reverses the block order and negates the
  exponents. That needs a transport lemma for `realStandardModule`; this is an option only.
- Twisting by `sgn(det)`. In Knapp 1994 (2.1a), printed p. 399, PDF p. 409, `D_ℓ` is induced
  from `SL₂(ℝ)` to `SL₂^±(ℝ)`; since `sgn(det)` is trivial on `SL₂(ℝ)`, this gives
  `D_ℓ ⊗ sgn(det) ≅ D_ℓ`. Tensoring a standard module of `GL₃(ℝ)` with `sgn(det)` therefore
  toggles the parity `ε` of its character block `sgn^ε |·|^s` and fixes its induction block.
  So the reducibility of the standard module of `[χ, D]` or `[D, χ]` does not depend on `ε`;
  the twist carries the composition factors for one parity to those for the other. Any
  explicit description of the composition series used in a proof has to respect this.

Uniqueness of the factor `J(y, x)` is the subject of
`RealStandardLanglandsQuotientStatement`, which may help with the `ws j = [y, x]` piece.

## The reduction: `realInducedPairFiltration_of_base`

Hypotheses: `hS : RealAdjacentFiltrationInStagesStatement`,
`hCI : RealCharacterInducedFiltrationStatement`,
`hIC : RealInducedCharacterFiltrationStatement`,
`hII : RealInducedInducedFiltrationStatement`. Conclusion:
`RealInducedPairFiltrationStatement`.

Proof. Take `n`, `pre`, `post`, `x`, `y`, the hypothesis `hind` that `x` or `y` is an
induction block, `hrank : realRank (pre ++ x :: y :: post) = n` and
`hxy : realBlockExponent x < realBlockExponent y`. By `hS n pre post x y hrank` it suffices to
prove `RealAdjacentFiltration (realRank [x, y]) [] [] x y`. Case analysis on `x` and `y`:

- two characters: impossible, since both disjuncts of `hind` say that a character block equals
  an induction block (`cases` on the equation);
- `x = .character c`, `y = .induced d`: `hCI c d hxy`;
- `x = .induced d`, `y = .character c`: `hIC d c hxy`;
- `x = .induced d`, `y = .induced e`: `hII d e hxy`.

In the last three cases `realRank [x, y]` reduces by definition to `3`, `3` and `4`, so the
terms have the required type without rewriting.
