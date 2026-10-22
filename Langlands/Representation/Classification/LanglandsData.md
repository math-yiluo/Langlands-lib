# Langlands data for `GL_n` over a p-adic field

Author: Worker 23.

This module defines the data of the Langlands classification of irreducible
representations of `GL_n(F)`, in three source forms, and the induced
representations they determine.

1. Tempered blocks with strictly decreasing real exponents (Kudla, Theorem 2.2.2).
2. Essentially square-integrable blocks with decreasing exponents (Henniart,
   section 2.8).
3. Precedence-ordered families of segments, with the special constituents of the
   segments as blocks: Kudla's Theorem 1.2.5 for Langlands quotients, and
   Zelevinsky's Theorem 6.1 for subrepresentations.

The Langlands quotient and Zelevinsky's representation are recorded only by
relations on a given representation `π`. The module asserts no existence or
uniqueness of quotients, no independence of the data, and no classification. It
contains definitions and their immediate consequences only.

All constructions take a p-adic field `F`, a realization `T : F.TopologicalData`,
and `ν = |det|` with the residue-normalized absolute value. Induction is the
published normalized block-factor induction `T.normalizedProductInductionFunctor`
of `Induction/BlockFactors`. It is normalized parabolic induction from the
standard upper block parabolic of the block shape, applied to the external
tensor product of the blocks.

## Twisted block induction

For an ordered block shape `B = (n_1, …, n_r)` of `n`, smooth representations
`σ_i` of `GL_(n_i)(F)` with carriers in `Type uV`, and real numbers `u_i`:

- `T.twistedBlocks B σ u` is the family `(ν^(u_1) σ_1, …, ν^(u_r) σ_r)`. Each
  member is the published `T.segmentFactor (σ i) (u i)`, the actual twist
  `g ↦ |det g|^(u_i) σ_i(g)`.
- `T.twistedProductInduced B σ u` is `i(ν^(u_1) σ_1, …, ν^(u_r) σ_r)` on
  `GL_n(F)`, with carrier in `Type (max uF uV)`.
  `twistedProductInduced_representation` identifies its representation with
  `T.normalizedProductInduced B` of the twisted family by `rfl`.
- `twistedProductInducedIso` sends isomorphisms `σ_i ≅ σ'_i` to an isomorphism of
  the induced objects.

The twisting character is the published `T.determinantPowerCharacter`, the real
power of `T.determinantNorm`. By `determinantNorm_coe` (by definition), its
absolute value of `det g` is `T.normalizedAbs (det g)`. This is the same
function as the `normalizedAbsoluteValue T` of `RankinSelberg/AnalyticStatement`
(`normalizedAbsoluteValue_apply`, also by definition).

## Tempered form

`T.TemperedLanglandsDatum n` consists of:

- an ordered block shape `shape = (n_1, …, n_r)` of `n`;
- smooth representations `blocks i` of `GL_(n_i)(F)` that are irreducible
  (`irreducible`) and tempered (`tempered`, the analytic `T.IsTempered` of
  `Classification/Tempered`);
- real exponents `exponent : Fin r → ℝ` with `u_1 > ⋯ > u_r` (`strictAnti`).

Its `standardModule` is `i(ν^(u_1) π_1, …, ν^(u_r) π_r)`. The relation
`IsLanglandsQuotient d π` says that `π` is an irreducible quotient of the
standard module. `IsLanglandsHead d π` adds that every irreducible quotient map
has the same kernel. `IsLanglandsHead.isLanglandsQuotient` drops the uniqueness
clause.

## Essentially square-integrable form

`T.SquareIntegrableLanglandsDatum n` consists of:

- an ordered block shape;
- irreducible blocks `π_i` that are essentially square-integrable
  (`T.IsEssentiallySquareIntegrable` of `Classification/Tempered`);
- for each block, the published `UnitaryExponentData` of `Classification/Essential`.
  This is a real `α(π_i)` together with an invariant positive definite form on
  `ν^(-α(π_i)) π_i`, so that `π_i = ν^(α(π_i)) π_u` with `π_u` unitary;
- the condition `α(π_1) ≥ ⋯ ≥ α(π_r)` (`antitone`).

`exponent i` is `α(π_i)`, and `induced` is `i(π_1, …, π_r)`, with
`induced_representation` by `rfl`. `IsLanglandsQuotient` and `IsLanglandsHead`
are the quotient and head relations for `i(π_1, …, π_r)`. The head form is the
relation satisfied by Henniart's `J(π_1, …, π_r)`.

`ν^(-α) π_i` is again essentially square-integrable, by the lemma
`IsEssentiallySquareIntegrable.realPowerTwist` of `Classification/Tempered`. So the fields express
Henniart's `π_u ∈ A_2` unitary. The exponent is carried as data. Its uniqueness
is a theorem that is not proved here.

## Segment form

- `T.segmentShape Δ h` is the ordered block shape `(deg Δ_1, …, deg Δ_r)` of `n`,
  given segments `Δ : Fin r → Segment` and `h : ∑ i, deg Δ_i = n`. Here
  `deg Δ = m r` is the published `Segment.degree`. Its block sizes are the
  degrees by definition (`segmentShape_size`), so representations of
  `GL_(deg Δ_i)(F)` are block factors without casts.
- `T.SegmentProductDatum n` consists of:
  - a number `length`;
  - segments `segments : Fin length → Segment` whose degrees add up to `n`
    (`degree_sum`);
  - representations `blocks i` of `GL_(deg Δ_i)(F)`, with carriers in
    `Type (max uF uV)`. That is the universe of the published segment relations.

  Derived from the datum:
  - `shape` is the segment shape;
  - `multisegment` is the multiset `{Δ_1, …, Δ_r}`, listed by `segments`
    (`multisegment_isOrdering`);
  - `induced` is `i(π_1, …, π_r)`, with `induced_representation`;
  - `IsPrecedenceOrdered` is the published condition that `Δ_i` does not precede
    `Δ_j` for `i < j`;
  - `HasSegmentHeads`: every `π_i` satisfies the published `IsSegmentHead`;
  - `HasSegmentSocles`: every `π_i` satisfies the published `IsSegmentSocle`.

  Relations on `d`:
  - `IsLanglandsQuotient d π` and `IsLanglandsHead d π`: the datum is
    precedence-ordered with segment heads, and `π` is an irreducible quotient
    (resp. the irreducible head) of `i(π_1, …, π_r)`.
  - `IsZelevinskySubrepresentation d π` and `IsZelevinskySocle d π`: the datum is
    precedence-ordered with segment socles, and `π` is an irreducible
    subrepresentation (resp. the irreducible socle).
  - Head implies quotient, and socle implies subrepresentation.
- `Multisegment.IsLanglandsHead a π` and `Multisegment.IsZelevinskySocle a π` hold
  when some datum whose multisegment is `a` satisfies the corresponding head or
  socle relation. They assert no independence of the chosen ordering.

## Source correspondence

- Kudla (1994), Theorem 2.2.2, printed pages 373--374 (PDF pages 383--384 of the
  *Motives* Part 2 volume): "(a) Every irreducible admissible representation π
  can be written as a quotient of an induced representation of the form
  ξ = I_P^G(π_1(x_1) ⊗ ⋯ ⊗ π_m(x_m)) where the π_i's are tempered
  representations and x_1 > x_2 > ⋯ > x_m are real numbers. (b) For a given π,
  the standard parabolic P, the tempered representations π_1, …, π_m (up to
  isomorphism) and the real numbers x_1 > x_2 > ⋯ > x_m are unique."
  - `π(x) = π ⊗ |det|^x` (printed page 367). `I_P^G` is normalized induction from
    the standard (upper) parabolic (printed page 368).
  - Tempered representations are irreducible (section 2.2, printed page 372).
  - This is `TemperedLanglandsDatum`, `standardModule` and `IsLanglandsQuotient`.
    Statement (a) is an existence theorem and (b) a uniqueness theorem. Neither
    is asserted.
- Kudla (1994), Theorem 1.2.2, printed page 369 (PDF page 379), and Theorem
  1.2.5, printed pages 370--371 (PDF pages 380--381): "Given segments
  Δ_1, …, Δ_r, assume that for i < j, Δ_i does not precede Δ_j. Then (a) the
  induced representation I(Q(Δ_1) ⊗ ⋯ ⊗ Q(Δ_r)) admits a unique irreducible
  quotient Q(Δ_1, …, Δ_r)." Here `Q(Δ)` is the unique irreducible quotient of
  `I(Δ)` (Theorem 1.2.2). This is `SegmentProductDatum.IsLanglandsHead`, with
  `HasSegmentHeads`, and `Multisegment.IsLanglandsHead` for the multiset form of
  (b).
- Henniart (2002), section 2.8, printed page 596 (PDF page 10): "Un élément π de
  A_2 s'écrit de façon unique sous la forme ν^{α(π)} π_u où π_u ∈ A_2 est
  unitaire et α(π) ∈ R. Soient r un entier ≥ 1 et π_1, …, π_r des éléments de
  A_2. Supposons qu'on ait (*) α(π_1) ≥ ⋯ ≥ α(π_r). Alors la représentation
  i(π_1, …, π_r) a un unique quotient irréductible J = J(π_1, …, π_r)". This is
  `SquareIntegrableLanglandsDatum` and its `IsLanglandsHead`.
- Zelevinsky (1980), Theorem 6.1(a), printed page 188 (PDF page 25): for
  segments with no `Δ_i` preceding `Δ_j` for `i < j`, "the representation
  ⟨Δ_1⟩ × ⋯ × ⟨Δ_r⟩ has a unique irreducible submodule; denote it by
  ⟨Δ_1, …, Δ_r⟩". Section 6.5, printed page 189: `⟨a⟩` for a multiset `a`. These
  are `SegmentProductDatum.IsZelevinskySocle`, with `HasSegmentSocles`, and
  `Multisegment.IsZelevinskySocle`.

Registered sources:

- `kudla-1994-local-langlands-nonarchimedean`, SHA256
  `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b`.
- `henniart-2002-characterization`, SHA256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
- `zelevinsky-1980-induced-ii`, SHA256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.

The tempered form is the standard-module shape that the Jacquet--Piatetski-Shapiro--Shalika
local factors of non-generic representations use. That source's scanned pages
were not read for this module, and it is not cited for these definitions.

## Derivations

- **Exponent order.** The sources order exponents from largest to smallest along
  the upper block diagonal. The fields use `StrictAnti` (Kudla) and `Antitone`
  (Henniart's (*)) on the block index.
- **Data, not classes.** Blocks are actual smooth representations, not
  isomorphism classes. The relations depend only on the induced representation.
  Relations on isomorphism classes, and independence of the representatives, are
  theorem obligations.
- **Segment form.** The segment form requires the blocks to satisfy the segment
  head (resp. socle) relation. It does not construct `Q(Δ_i)` or `⟨Δ_i⟩`, whose
  existence is a theorem. A multisegment relation chooses one precedence-ordered
  ordering. Independence of the ordering is Kudla's Theorem 1.2.5(b) and
  Zelevinsky's Proposition 6.4, and is not asserted.

## Universes and scope

The tempered and square-integrable blocks have carriers in `Type uV`, and their
induced representations in `Type (max uF uV)`. Segment blocks have carriers in
`Type (max uF uV)`, the universe of the published segment relations. Their
induced representation stays in `Type (max uF uV)`. Every p-adic field, every
realization, every `n` and every ordered block shape is covered.

## Not claimed

The module proves none of the following, which are separate theorem obligations:

- existence or uniqueness of Langlands quotients, Henniart's `J` or Zelevinsky's
  `⟨a⟩`;
- uniqueness of the Langlands data or independence of orderings;
- that segment heads are essentially square-integrable;
- that tempered representations are irreducibly induced from square-integrable
  ones;
- the compatibility of the three forms;
- any classification bijection.
