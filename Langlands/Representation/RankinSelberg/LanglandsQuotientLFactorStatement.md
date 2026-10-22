# L-factors of pairs through the Langlands classification

Author: Worker 11. This module, in namespace `Langlands.RankinSelberg`, states
the L-factor results of Section 9 of Jacquet, Piatetski-Shapiro and Shalika,
*Rankin-Selberg convolutions*, Amer. J. Math. 105 (1983):

- Proposition (9.4), display (3): the L-factor of a pair of induced
  representations of Langlands' type is the product of the L-factors of the
  pairs of their blocks.
- Display (4): a generic irreducible quotient has the L-factor of its
  standard module.
- The definition of `L(s, π × σ)` for every pair of irreducible admissible
  representations.
- Theorem (9.5), the biadditivity of this L-factor, in its product form.

The factors are the rank-symmetric relation `IsPadicSymmetricLPolynomial` of
the module `PadicPairFactors`. The Langlands data, standard modules and
Langlands quotients are those of the published module
`Classification/LanglandsData`. The module defines two relations, with their
uniqueness lemmas, and five statements. None of the statements is proved.

## Source

JPSS 1983 (printed page = PDF page + 365), read from the page images.

- **(9.4), printed page 458.** `Q` is an *upper* parabolic subgroup of `G_r`
  of type `(r_1, …, r_m)`. Each `π_(i,0)` is a tempered representation of
  `G_(r_i)`, and `u_1 > u_2 > ⋯ > u_m` are real numbers. With
  `π_i = π_(i,0) ⊗ α^(u_i)` (`α = |det|`), display (1) is
  `ξ = Ind(G_r, Q; π_1, …, π_m)`. Similar data for `G_t` give `R` of type
  `(t_1, …, t_n)`, `σ_i = σ_(i,0) ⊗ α^(v_i)` and, in display (2),
  `η = Ind(G_t, R; σ_1, …, σ_n)`. "As we have noted in Section 8 tempered
  representations are generic. Thus by (2.3) `ξ` and `η` are both of
  Whittaker type."
  **Proposition.** With the above notations, display (3) reads
  `L(s, ξ × η) = L(s, π_i × σ_j)`, "the product taken for `1 ≤ i ≤ m`,
  `1 ≤ j ≤ n`". The printed display shows no product sign; the sentence after
  it makes the right side the product over all pairs `(i, j)`.
  Following the Proposition, an arbitrary irreducible admissible `π` (resp.
  `σ`) "is uniquely representable as a quotient of a representation `ξ`
  (resp. `η`) of Langland's type". When `π` is generic, `π` and `ξ` have the
  same Whittaker model, and similarly for `σ`. Hence display (4):
  `L(s, ξ × η) = L(s, π × σ)`. "In any case one can take (4) as a definition
  of `L(s, π × σ)` for any pair `π, σ` of irreducible, admissible
  representations."
- **(8.4), printed page 451.** A tempered representation is
  `Ind(G_r, Q; π_1, …, π_m)` with square-integrable `π_i`, and a
  (quasi-)tempered representation is automatically irreducible.
- **(9.5), printed pages 462-463.**
  - `𝔄_r` is the set of classes of irreducible admissible representations of
    `GL_r(F)`, and `SQ_r` its subset of quasi-square-integrable ones.
  - `Λ` is the set of formal sums `λ = τ_1 + ⋯ + τ_p` (display (1)) with
    `τ_i ∈ SQ`.
  - Write `τ_i = σ_i ⊗ α^(s_i)` with `σ_i` unitary and `s_i` real, ordered so
    that `s_1 ≥ ⋯ ≥ s_p`. Then `π[λ]` is "the unique irreducible quotient" of
    `ξ = Ind(G_r, Q; τ_1, …, τ_p)` (display (3)).
  - `λ ↦ π[λ]` is a bijection from `Λ` to `𝔄`, and transport of structure
    gives an addition `⊞` on `𝔄`.
  - **Theorem.** `L(s, π × σ)` is biadditive:
    `L(s, (π ⊞ π') × σ) = L(s, π × σ) L(s, π' × σ)`, and likewise in `σ`, for
    all `π, π', σ, σ' ∈ 𝔄`. "The proof is an immediate consequence of
    Propositions (8.4) and (9.4)."

Henniart, *Une caractérisation de la correspondance de Langlands locale pour
GL(n)*, Bull. SMF 130 (2002), read from the text layer (printed page =
0-based PDF index + 587):

- **§2.5, printed page 594.** `i(π_1, …, π_r)` is normalized parabolic
  induction from the parabolic subgroup of block upper triangular matrices
  with diagonal blocks of sizes `n_1, …, n_r`.
- **§2.8, printed page 596.** An essentially square-integrable `π` is
  `ν^(α(π)) π_u` with `π_u` unitary and `α(π)` real. If
  `α(π_1) ≥ ⋯ ≥ α(π_r)`, then `i(π_1, …, π_r)` has a unique irreducible
  quotient `J(π_1, …, π_r)`. For `π = ∑ π_i` and `π' = ∑ π'_j` the formulas
  include `L(s, π × π') = ∏_(i,j) L(s, π_i × π'_j)`. The same paragraph
  gives products for `γ` and `ε`, and refers to the introduction of JPSS for
  the classification.

## Definitions

Throughout, `F : PadicField p` carries its canonical topological data
(residue cardinality `q`, normalized absolute value), `ψ` is a
`UnitaryAdditiveCharacter` of `F`, and `ν` is an additive Haar measure.
`L(s, π × σ) = 1 / P(q^(-s))`, and `IsPadicSymmetricLPolynomial` reads the
pair with the larger rank first, as in JPSS (2.12).

- `IsPadicRankLPolynomial F ψ ν π σ P`, for `π` on `GL_n(F)` and `σ` on
  `GL_t(F)` of arbitrary ranks: `IsPadicSymmetricLPolynomial F ψ ν π σ P`
  when `n = n' + 1` and `t = t' + 1`, and `False` when a rank is zero.
  - Purpose: it applies the factor relation to the blocks of the Library's
    block shapes, whose sizes `B.size i` are positive (`BlockShape.positive`)
    but not syntactically successors. For actual blocks the `False` branch
    never applies.
  - `isPadicRankLPolynomial_succ` is the unfolding at successor ranks.
  - `IsPadicRankLPolynomial.unique` proves that `P` is unique.
- `IsLanglandsPairLPolynomial F ψ ν π σ P`, for smooth representations `π` of
  `GL_(r+1)(F)` and `σ` of `GL_(t+1)(F)` with carriers in universes
  `max uF uV` and `max uF uW`, is the conjunction of three conditions:
  - there is a `TemperedLanglandsDatum` `d` of rank `r + 1` (blocks in
    universe `uV`) with `d.IsLanglandsQuotient π`;
  - there is such a datum `e` of rank `t + 1` (blocks in `uW`) for `σ`;
  - for all such `d` and `e`, `IsPadicSymmetricLPolynomial F ψ ν` holds for
    `d.standardModule` and `e.standardModule` with polynomial `P`.

  This is JPSS's definition "(4)": `L(s, π × σ) = L(s, ξ × η)` with `ξ`, `η`
  the standard modules of which `π`, `σ` are quotients.
  `IsLanglandsPairLPolynomial.unique` proves that `P` is unique.

The Library objects used here:

- A `TemperedLanglandsDatum` has these fields:
  - an ordered block shape;
  - irreducible tempered blocks `π_(i,0)`;
  - real exponents `u_1 > ⋯ > u_m` (`StrictAnti`).
- Its `standardModule` is normalized induction from the standard *upper* block
  parabolic of the twisted blocks `twistedBlocks`, `ν^(u_i) π_(i,0)` with
  `ν = |det|` normalized.
- `IsLanglandsQuotient π` says that `π` is irreducible and that there is a
  surjective intertwining map from the standard module onto `π`. It asserts
  neither existence nor uniqueness of such a quotient.
- A `SquareIntegrableLanglandsDatum` has these fields:
  - an ordered block shape;
  - irreducible essentially square-integrable blocks `τ_i`;
  - for each `τ_i`, a real `α(τ_i)` such that `ν^(-α(τ_i)) τ_i` carries an
    invariant positive definite form, with `α(τ_1) ≥ ⋯ ≥ α(τ_p)`.
- Its `induced` is the normalized induction `i(τ_1, …, τ_p)` from the upper
  block parabolic. Its `IsLanglandsQuotient` is again "irreducible quotient".

The statements quantify over every prime `p`, every `F : PadicField p`, every
`ψ`, and every `ν` in the published
`LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ`.

- `LanglandsTypeLFactorStatement` (display (3)): for all `r`, `t` and all
  tempered Langlands data `d` of `GL_(r+1)(F)` and `e` of `GL_(t+1)(F)`,
  there are a polynomial `P` and polynomials `Q i j`
  (`i < d.shape.length`, `j < e.shape.length`) such that:
  - `P` is the symmetric L-polynomial of `(d.standardModule,
    e.standardModule)`;
  - `Q i j` is the L-polynomial (`IsPadicRankLPolynomial`) of the twisted
    blocks `ν^(u_i) π_(i,0)` and `ν^(v_j) σ_(j,0)`;
  - `P = ∏_i ∏_j Q i j`.
- `GenericLanglandsQuotientLFactorStatement` (display (4)): for all data `d`,
  `e` as above and smooth `π`, `σ` with `d.IsLanglandsQuotient π`,
  `e.IsLanglandsQuotient σ`, `IsGeneric ψ r π` and `IsGeneric ψ t σ`, there
  is a `P` that is the symmetric L-polynomial both of the standard modules and
  of `(π, σ)`.
- `LanglandsPairLFactorExistenceStatement` (the definition after (4)): for
  all `r`, `t` and smooth `π` of `GL_(r+1)(F)`, `σ` of `GL_(t+1)(F)` that are
  irreducible (`Representation.IsIrreducible`) and admissible
  (`SmoothRep.IsAdmissible`), there is `P` with
  `IsLanglandsPairLPolynomial F ψ ν π σ P`.
- `SquareIntegrableDataLFactorStatement` (Theorem (9.5), product form): for
  all `r`, `t`, essentially square-integrable data `d` of `GL_(r+1)(F)` and
  `e` of `GL_(t+1)(F)`, and smooth `π`, `σ` with `d.IsLanglandsQuotient π`
  and `e.IsLanglandsQuotient σ`, there are `P` and `Q i j` such that:
  - `IsLanglandsPairLPolynomial F ψ ν π σ P`;
  - `Q i j` is the L-polynomial (`IsPadicRankLPolynomial`) of the blocks
    `(τ_i, μ_j)`;
  - `P = ∏_i ∏_j Q i j`.
- `LanglandsQuotientLFactorStatement` is the conjunction of the four
  statements.

## Interpretation

- **Ranks.** Ranks are written `r + 1` and `t + 1`: the factors exist only in
  positive rank. JPSS's `m` and `n` (numbers of blocks) are
  `d.shape.length` and `e.shape.length`.
- **Parabolic and induction.** JPSS (9.4) use an upper parabolic subgroup, as
  does the Library's `standardModule` (and Henniart §2.5), so no change of
  convention is involved. Strictly decreasing exponents are the field
  `strictAnti` of the datum. The induction is the published
  `normalizedProductInductionFunctor`: right translation on functions
  transforming by the block representations with the square root of the
  modulus, as in JPSS Section 1, displays (8)-(11), printed pages 376-377.
- **Tempered blocks.** JPSS (8.4), printed page 451, define a tempered
  representation as `Ind(G_r, Q; π_1, …, π_m)` with square-integrable `π_i`.
  They add that "a (quasi-) tempered representation is automatically
  irreducible [H.J. II]". The Library's datum requires each block to be
  irreducible and tempered in the analytic sense of `IsTempered` (matrix
  coefficients in `L^(2+ε)` modulo the center). The two descriptions give the
  same irreducible representations of `GL_n(F)`, but that comparison is not
  proved in the Library.
- **Factor of the standard modules.** JPSS observe that `ξ` and `η` are of
  Whittaker type ((2.3), and genericity of tempered representations). Their
  L-factor is therefore the one of Theorem 2.7. The statements do not assume
  Whittaker type: the existence of `P` is part of each conclusion. Neither
  (2.3) nor the genericity of tempered representations is proved in the
  Library.
- **Genericity.** `IsGeneric ψ r π` is the published predicate: irreducible,
  admissible, and with a nonzero Whittaker functional for `standardCharacter
  ψ`. The symmetric L relation uses `ψ`-functionals for the representation of
  larger rank and `ψ⁻¹`-functionals for the other. Genericity for `ψ` and for
  `ψ⁻¹` are equivalent (conjugation by a diagonal matrix), so requiring
  `IsGeneric ψ` of both is JPSS's "generic". This equivalence is not proved
  in the Library.
- **The definition for all pairs.** `IsLanglandsPairLPolynomial` quantifies
  over *every* pair of data with `π`, `σ` as quotients, not over a chosen
  one. JPSS's "uniquely representable" (the Langlands classification) makes
  the datum unique up to isomorphism of its blocks. Isomorphic block families
  give isomorphic standard modules (`twistedProductInducedIso`), and the L
  relation is invariant under equivalence
  (`IsPadicSymmetricLPolynomial.congr_equiv`). Hence JPSS's definition
  satisfies the relation. Conversely, by the proved uniqueness lemma the
  relation determines `P`. The classification itself is not proved in the
  Library.
- **Universes.** The tempered or square-integrable blocks of a datum have
  carriers in the fixed universe `uV` (resp. `uW`), and the standard modules
  and `π`, `σ` in `max uF uV` (resp. `max uF uW`), as in the Library's
  datum.
  - The existence statement thus also asserts that the blocks of the
    Langlands datum of `π` can be realized in universe `uV`.
  - This is a consequence of the classification, not a statement of JPSS: an
    irreducible smooth representation of `GL_n(F)` is spanned by the
    translates of a vector fixed by an open subgroup `K`, indexed by the
    countable set `GL_n(F)/K`. So it has a model of countable dimension in
    every universe.
- **Theorem (9.5) in product form.** JPSS state biadditivity under `⊞`,
  defined through the bijection `λ ↦ π[λ]` from `Λ` to `𝔄`. Given that
  bijection, biadditivity is equivalent to the product form stated here:
  - Biadditivity gives the product form by induction on the numbers of
    summands, since `π[τ] = τ` for a single `τ ∈ SQ`.
  - The product form gives biadditivity, since `π[λ] ⊞ π[λ'] = π[λ + λ']`.

  The product form is the formula of Henniart §2.8. The bijection
  ([B-W], [A.S.] in JPSS) is not proved in the Library.
  - JPSS's `π[λ]` is the unique irreducible quotient of the induced
    representation with `s_1 ≥ ⋯ ≥ s_p`. This is the Library's
    `SquareIntegrableLanglandsDatum`: the `antitone` exponents `α(τ_i)` are
    JPSS's `s_i`.
  - The statement quantifies over every irreducible quotient. By the
    uniqueness of that quotient this is JPSS's `π[λ]`.
  - The left side is the L-factor defined through tempered data
    (`IsLanglandsPairLPolynomial`).
  - The right side uses, for each pair of blocks, the L-factor of Theorem 2.7.
    The blocks are generic (essentially square-integrable representations
    are twists of tempered ones, which are generic by JPSS (9.4)), so by
    display (4) the two definitions agree on them.
  - JPSS's proof combines Proposition (8.4) with Proposition (9.4).
    Proposition (8.4) says that for tempered `Ind(π_1, …, π_m)` and
    `Ind(σ_1, …, σ_n)` with square-integrable blocks the L-factor is
    `∏ L(s, π_i × σ_j)`.
- **Only the L-factor.** JPSS define only `L(s, π × σ)` for nongeneric pairs.
  The `γ` and `ε` products of Henniart §2.8 are not stated here.
- **Measures and field.** As in the other JPSS units, the statements take `ν`
  self-dual for `ψ` (`SelfDualHaar`); the relations accept any additive Haar
  measure. `F` is a p-adic field (`PadicField`) because the canonical
  topological data and the Langlands data are published only for p-adic
  fields; JPSS work over any nonarchimedean local field.
- **Not stated.** These parts of the source are not stated:
  - the claim that `π` is generic if and only if `π ≃ ξ` ([J-S III]);
  - the uniqueness of the Langlands datum;
  - Henniart's contragredient formula `J^∨ ≃ J(π_r^∨, …, π_1^∨)`.

## Lean checks

`lean_check` of the module with declaration
`Langlands.RankinSelberg.LanglandsQuotientLFactorStatement`:

- 0 errors and 0 warnings.
- The declaration is a definition returning `Prop`, with universe parameters
  `uF`, `uV`, `uW`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
