# Equal-exponent grouping of square-integrable Langlands blocks

Author: Worker 175.

`Langlands.Classification.squareIntegrableEqualExponentGrouping` proves the
complete published proposition
`Langlands.Classification.SquareIntegrableEqualExponentGrouping.{uF,uV} F T`
from [TemperedBlockStatement](TemperedBlockStatement.md). Its outer telescope is
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
The field and carrier universes remain independent. All input and grouped
representation carriers have universe `max uF uV`, which is also the universe
of their induced representations.

For every positive-rank square-integrable Langlands datum, the theorem proves
analytic square-integrability at each chosen unitary exponent and constructs
the entire tempered datum, monotone surjective grouping map, ordered fiber
bijections, rank equalities, within-run normalized-product isomorphisms, and
isomorphism of the original induced representation with the new standard
module. The public theorem has no additional hypothesis.

## Normalization and construction of the new blocks

The closing proof first applies the published
`chosenUnitarySquareIntegrability` theorem to each original block, using its
positive rank, irreducibility, essential square-integrability and chosen
`UnitaryExponentData`. This supplies the first conjunct of the target in its
original analytic meaning.

The argument behind this imported theorem is described in
[ChosenUnitaryNormalizationProof](ChosenUnitaryNormalizationProof.md).
Essential square-integrability supplies an exponent `s` and a unitary scalar
central character after normalization. The invariant positive form at the
chosen exponent `a` forces the scalar action at a uniformizer matrix to have
modulus one. Positive block rank and the normalized absolute value then give
`s = a`. Thus the use of the chosen exponent is a proved analytic
normalization, rather than a definitional identification.

The private `groupedTemperedBlocksWithSource` helper applies the published
`orderedExponentGrouping` theorem to the antitone exponent function. It obtains
the outer shape `D`, strictly antitone exponent function `b`, monotone
surjection `q`, inner shapes `S j`, increasing fiber bijections `e j`, exact
rank equalities `h j k`, and the standard ambient-coordinate identity.
[OrderedExponentGroupingProof](OrderedExponentGroupingProof.md) constructs
these data by ordering the finite exponent range and increasingly enumerating
each complete fiber, with ranks given by the corresponding positive sums.

Put `δ i = T.segmentFactor (d.blocks i) (-d.exponent i)`.
Twisting preserves irreducibility by `isIrreducible_twist_iff`; the datum's
unitary-exponent fields supply actual invariant positive forms on `δ i`.
The analytic normalization above supplies square-integrability. Equality
elimination transports all three properties to
`τ j k = (h j k).symm ▸ δ (e j k).val`.

The published `squareIntegrableBlockInduction.{uF,uV} F T` applies to each
positive-rank inner shape. Its irreducibility and analytic temperedness
conclusions are the corresponding fields of the constructed datum `t`, whose
blocks are precisely the normalized products of the `τ j`. Its third
conclusion is the original `T.IsTempered`, not an exponent-based replacement.
The imported theorem also proves unitarizability of these products; no
constructor assumption supplies any of these conclusions. See
[SquareIntegrableBlockInductionProof](SquareIntegrableBlockInductionProof.md)
for its irreducibility, invariant-form and analytic-induction arguments.

Set `t.shape = D` and `t.exponent = b`. The finite grouping theorem supplies
`t.strictAnti`, monotonicity and surjectivity of `q`, exponent preservation,
and each strictly increasing fiber enumeration. Every within-run product
isomorphism in the target is now the identity on the block used to define
`t`. Strict antitonicity makes `b` injective, so exponent preservation makes
the fibers of `q` exactly the equal-exponent classes. Monotonicity makes
these classes consecutive, and surjectivity makes every new class nonempty.
These are the maximal consecutive equal-exponent runs.

## Isomorphism of the induced representations

The private `groupedCommonExponentIso` specializes the published
`twistedProductCharacterTwist` theorem to the smooth unit character
`|.|^s` and constant old exponents `-s`. The resulting comparison identifies
the `s` twist of the product of the `-s` twists with the product of the
double-twisted original factors. `realPowerTwist_neg_cancel` identifies each
double twist with its original factor. The normalized product induction
functor maps these factor isomorphisms, and composing inverses yields

```text
product(σ) ≅ ν^s product(ν^(-s) σ).
```

For the full source comparison, combine the fiber bijections into the
sigma equivalence `E` using `Equiv.sigmaCongrRight` and
`Equiv.sigmaFiberEquiv q`. Apply the published
`Parabolic.orderedProductRegrouping.{uF,max uF uV} F T` to the original
factors, `E`, the exact rank equalities and the standard-coordinate identity.
This gives an actual isomorphism from the original normalized product to
outer normalized induction of the within-run products of original factors.
[OrderedProductRegroupingProof](../Parabolic/OrderedProductRegroupingProof.md)
constructs it from the coordinate comparison, equivariant tensor regrouping,
normalized induction in stages, and refined induction/tensor comparison.

On each fiber, exponent preservation gives
`d.exponent (e j k).val = b j`. Equality elimination proves that segment
twisting commutes with the displayed rank transport. The common-exponent
isomorphism therefore identifies that run's product with
`T.segmentFactor (t.blocks j) (b j)`. Outer normalized product induction maps
these block isomorphisms. Composing with the regrouping isomorphism proves
`d.induced ≅ t.standardModule`. A final congruence conversion identifies the
dependent factor families without expanding the induced function spaces.

All maps use actual smooth representations, categorical isomorphisms and the
specified equality transports. The standard upper parabolics, positive
half-modulus covariance and right-translation actions are inherited from
the published induction constructions.

## Original sources and provenance

This is a derived composition of published Library proofs with explicit
finite-fiber bookkeeping. The original grouping observation is in Kudla,
*The local Langlands correspondence: the non-archimedean case* (1994),
§2.2, printed p.373: equations (2.2.2)–(2.2.3) and the equal-exponent
observation before Theorem 2.2.2. Proposition 2.2.1 on that page supplies
the square-integrable induction result used by the mathematical argument.
The finite shapes, complete ordered fibers and rank transports here make
that observation explicit; they are not attributed to an exact displayed
proposition in the source. Section 1.1, printed pp.367–368, fixes the
normalized upper-induction convention.

Henniart (2002), §§2.5 and 2.8, printed pp.595–596, supplies the norm-twist
and unitary-normalization context. The arbitrary-invariant-form
central-character proof used by the normalization dependency is an internal
derivation, as its paired Markdown explains. Bernstein–Zelevinsky (1977),
§1.8 and Proposition 1.9(f), printed pp.444–445, supplies the smooth
normalized-induction and character-compatibility convention; §2.2,
printed p.446, fixes ordered upper GL blocks.

Worker 175 read these original passages during the prerequisite development.
The retained registered sources and SHA-256 fingerprints are:

| Source ID | Read passage | SHA-256 |
| --- | --- | --- |
| `kudla-1994-local-langlands-nonarchimedean` | Printed pp.367–368,372–374; whole-volume PDF pp.377–378,382–384 | `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b` |
| `henniart-2002-characterization` | Printed pp.595–596; PDF pp.9–10 | `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306` |
| `bernstein-zelevinsky-1977-induced-i` | Printed pp.444–446; PDF pp.5–7 | `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092` |

The source boundaries in
[TemperedBlockStatement](TemperedBlockStatement.md) are retained. In
particular, the analytic and invariant-form input is supplied by proved
Library theorems; a literature citation, unitary central character or
Jacquet's Hilbert-space formulation is not substituted for those proofs.
The local assembly uses no regular-exhaustion theorem. Only this new
Lean/Markdown pair is contributed; the target statement and its imports are
unchanged.
