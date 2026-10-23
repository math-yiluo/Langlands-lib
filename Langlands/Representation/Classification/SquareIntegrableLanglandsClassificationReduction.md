# Reduction of the square-integrable Langlands classification for GL_n

Author: Worker 7.

This module proves that the published proposition
`Langlands.Classification.SquareIntegrableLanglandsClassification.{uF, uV} F T`
(module `MultisegmentClassificationStatement`, the block form of Henniart
2002, §2.8) follows from four other published propositions:

| Hypothesis | Library declaration (module) | Content |
| --- | --- | --- |
| `hgroup` | `SquareIntegrableEqualExponentGrouping.{uF, uV} F T` (`TemperedBlockStatement`) | Unitarily normalized blocks are square-integrable. Blocks with equal exponent group into regular tempered data. The induced representation is isomorphic to the grouped standard module. |
| `hTBU` | `TemperedBlockUniqueness.{uF, uV} F T` (`TemperedBlockStatement`) | Two products of irreducible unitarizable square-integrable blocks are isomorphic iff the blocks match up to permutation, rank equality and isomorphism. |
| `hhead` | `GLRegularLanglandsHeadExistenceStatement.{uF, uV}` (`RegularLanglandsStatement`) | Every regular-positive tempered standard module has an irreducible head. |
| `hdata` | `GLRegularLanglandsDataUniquenessStatement.{uF, uV}` (`RegularLanglandsStatement`) | Isomorphic irreducible quotients of two such standard modules have the same ordered ranks and exponents, and isomorphic tempered blocks. |

The main theorem is conditional on all four hypotheses. It does not prove any
of them. They are separate proof targets in the Library. The module assumes
nothing else. In particular it does not use
`EssentialSquareIntegrabilityExponentUniqueness`: the needed equality of
unitary exponents is proved here from actual central characters.

## Main theorem

```lean
theorem squareIntegrableLanglandsClassification_of_regular
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (hgroup : SquareIntegrableEqualExponentGrouping.{uF, uV} F T)
    (hTBU : TemperedBlockUniqueness.{uF, uV} F T)
    (hhead : GLRegularLanglandsHeadExistenceStatement.{uF, uV})
    (hdata : GLRegularLanglandsDataUniquenessStatement.{uF, uV}) :
    SquareIntegrableLanglandsClassification.{uF, uV} F T
```

The universes are the target statement's: data, blocks and quotients all have
carriers in `max uF uV`. The two regular-chamber hypotheses quantify over every
prime, p-adic field and topological realization. The proof uses them only at
the given `F` and `T`.

## Literature route

Henniart 2002 §2.8 (p.596, PDF page 10) states the target. For `π_i` essentially
square-integrable with `α(π_1) ≥ … ≥ α(π_r)`, the representation
`i(π_1, …, π_r)` has a unique irreducible quotient `J(π_1, …, π_r)`. Its
isomorphism class depends only on the unordered family of the `π_i`. Henniart
refers to his references [1] (Casselman) and [6, Intr.]
(Jacquet–Piatetski-Shapiro–Shalika) for this classification.

The implemented route is Kudla 1994 §2.2 (printed pp.372–374, PDF pages
382–384):

- Proposition 2.2.1 and equation (2.2.2): products of square-integrable
  representations are irreducible tempered.
- Equation (2.2.3) and the following remark: consecutive equal exponents can be
  merged into one tempered block.
- Theorem 2.2.2(a)–(b): Langlands quotients of regular-positive tempered
  standard modules exist and determine their data. Silberger 1978, Theorem 4.1,
  proves this for general p-adic reductive groups.

The published statement Markdown of `TemperedBlockStatement` and
`RegularLanglandsStatement` gives the exact source correspondence for the four
hypotheses. This module adds only the deduction between them.

## Declarations

All names are in `Langlands.Classification`.

### Rank-transported isomorphism

- `RankIso A B`, for `A` on `GL_m(R)` and `B` on `GL_m'(R)`, means
  `∃ h : m = m', Nonempty ((h ▸ A) ≅ B)`. This is exactly the per-block
  comparison in `SquareIntegrableLanglandsClassification`,
  `TemperedBlockUniqueness` and `GLRegularLanglandsDataUniquenessStatement`.
- `RankIso.iff_nonempty_iso`, `of_iso`, `refl`, `symm`, `trans`, `rank_eq` and
  `cast` show that this is an equivalence relation that reduces to ordinary
  isomorphism at equal rank. `cast` relates a representation to its transport
  along a rank equality.
- `exists_rank_eq_iff` turns the displayed form
  `∃ h : ∀ i, m i = m' (e i), ∀ i, Nonempty ((h i ▸ σ i) ≅ τ (e i))`
  into `∀ i, RankIso (σ i) (τ (e i))`, and back.
- `RankIso.segmentFactor` and `RankIso.of_segmentFactor`: rank isomorphism is
  preserved by the twist `T.segmentFactor · s`, and twisting both sides by
  `-s` can be undone. `segmentFactorCancelIso` gives the isomorphism
  `ν^s (ν^(-s) A) ≅ A` (from `realPowerTwist_cancel_neg`) used for the second
  statement.
- `RankIso.block_iff`: irreducibility, square-integrability and
  unitarizability (the block hypotheses of `TemperedBlockUniqueness`) transfer
  along `RankIso`.

### Heads and exponents

- `nonempty_iso_of_isIrreducibleHead`: if `S` has an irreducible head, any two
  irreducible quotients of `S` are isomorphic. Both quotient maps have the
  head kernel (`IsIrreducibleHead.headKernel_eq`). Each quotient is therefore
  equivalent to `S` modulo that kernel (`headEquivOfSurjective`).
- `exponent_eq_of_unitaryCentralCharacter`: Suppose `ν^(-s) ρ` and `ν^(-s') ρ`
  both have unitary central characters, `ρ` has a nonzero vector, and the
  positive character `ν` is not `1` at some central `z`. Then `s = s'`. Act
  on one nonzero vector. The two central characters differ at `z` by the
  positive real factor `ν(z)^(s - s')`, and both have norm one. So
  `(s - s') log ν(z) = 0`.
- `exponent_eq_of_isSquareIntegrable`: if two real-power twists
  `ν^(-s) ρ` and `ν^(-s') ρ` of a positive-rank GL_m representation with a
  nonzero vector are square-integrable, then `s = s'`. Square-integrability
  (`T.IsSquareIntegrable`, against a Haar measure obtained from
  `T.exists_isHaarMeasure_centralQuotient`) provides unitary central
  characters. Take `z` the scalar matrix of the uniformizer. Then
  `|det z| = q^(-m) ≠ 1` (`T.determinantNorm_scalar`,
  `T.normalizedAbs_uniformizer`, `T.residueCardinality_gt_one`).
- `RankIso.exponent_eq`: rank-isomorphic positive-rank irreducible blocks whose
  normalizations by `-s` and `-s'` are square-integrable have `s = s'`. An
  irreducible representation has a nonzero vector
  (`FiniteIndexRestriction.exists_ne_zero`).
- `normalized_block_of_isSquareIntegrable`: for a square-integrable Langlands
  datum `d`, consider the normalized block `ν^(-α(π_i)) π_i`, that is
  `T.segmentFactor (d.blocks i) (-d.exponent i)`. If it is square-integrable,
  it satisfies all three block hypotheses of `TemperedBlockUniqueness`:
  - irreducibility comes from `isIrreducible_twist_iff` and `d.irreducible`;
  - unitarizability comes from the invariant positive form stored in
    `d.unitaryExponent i`.

### Products

- `rankIso_productInduced_iff`: `TemperedBlockUniqueness` restated with
  `RankIso` for products over block shapes of possibly different total ranks.
  Matching blocks force equal total ranks, because block sizes sum to the
  total rank.
- `nonempty_twistedProductInduced_iso`: Suppose two twisted products
  `T.twistedProductInduced B σ u` and `T.twistedProductInduced C τ u'` have
  blocks and exponents that match along an order isomorphism
  `Fin B.length ≃o Fin C.length`. Then the products are isomorphic. An order
  isomorphism between `Fin` types is the identity, so the shapes and exponents
  agree. `twistedProductInducedIso` then applies.

### The two directions

- `exists_rankIso_of_nonempty_iso` (isomorphic quotients ⇒ matching blocks).
  Let `π`, `π'` be irreducible quotients of `d.induced` and `d'.induced`, with
  `π ≅ π'`.
  1. `hgroup` gives regular tempered data `t`, `t'` and grouping maps `q`, `q'`
     with `d.induced ≅ t.standardModule` and `d'.induced ≅ t'.standardModule`.
     So `π`, `π'` are Langlands quotients of `t`, `t'`
     (`IsIrreducibleQuotient.of_equiv`).
  2. `hdata` gives an order isomorphism `a` of the grouped indices with equal
     exponents and rank-isomorphic tempered blocks.
  3. Each tempered block `t.blocks j` is the product of the normalized blocks of
     its fibre `q⁻¹(j)`. These satisfy the block hypotheses by
     `normalized_block_of_isSquareIntegrable` and `hgroup`'s first conjunct.
     `rankIso_productInduced_iff` then gives a bijection between the fibres
     over `j` and `a j` with rank-isomorphic normalized blocks.
  4. Matched blocks have equal exponents, since both equal the common group
     exponent. `RankIso.of_segmentFactor` therefore untwists the normalized
     blocks to `d.blocks i` and `d'.blocks i'`.
  5. The fibrewise bijections assemble into one bijection
     `Fin d.shape.length ≃ Fin d'.shape.length` (`Equiv.ofFiberEquiv`).
- `nonempty_iso_of_rankIso` (matching blocks ⇒ isomorphic quotients).
  Let `e` match the blocks of `d` and `d'` by `RankIso`.
  1. Matched blocks have equal unitary exponents (`RankIso.exponent_eq`, using
     `hgroup`'s first conjunct for both data).
  2. Hence the grouped data `t`, `t'` from `hgroup` have the same exponent set.
     Their strictly decreasing exponents give an exponent-preserving bijection,
     promoted to an order isomorphism `a` by
     `TemperedLanglandsDatum.orderIsoOfExponentEquiv`. The map `e` sends the
     fibre of `q` over `j` onto the fibre of `q'` over `a j`.
  3. On each fibre, the twisted blocks match by `RankIso.segmentFactor`. So
     `rankIso_productInduced_iff` matches the tempered blocks `t.blocks j` and
     `t'.blocks (a j)`. `nonempty_twistedProductInduced_iso` then gives
     `t.standardModule ≅ t'.standardModule`.
  4. Then `π` and `π'` are both irreducible quotients of `t.standardModule`.
     `hhead` gives it an irreducible head, so
     `nonempty_iso_of_isIrreducibleHead` gives `π ≅ π'`.
- `squareIntegrableLanglandsClassification_of_regular` combines the two
  directions.

## Provenance and dependencies

The `RankIso` definition and its API are internal infrastructure. They restate
the rank-transported isomorphism already used in the published statements. The
theorems are derived: they compose published definitions and propositions and
assert no new literature claim. The literature in the table above records
where the hypotheses come from. It is not an independent source for any
declaration here.

The module was developed against Library commit
`0bfd14e8bc613b7c9562aa7ee70086679af1e1f9`. It imports:

- `Classification.MultisegmentClassificationStatement`: the target
  proposition.
- `Classification.TemperedBlockStatement`: grouping and tempered block
  uniqueness.
- `Classification.RegularLanglandsStatement`: regular head existence and data
  uniqueness.
- `Classification.RegularLanglandsOrder`: `orderIsoOfExponentEquiv`.
- `Classification.CanonicalConstituents`: `headEquivOfSurjective` and the head
  kernel.
- `LocalField.Normalization.Proof` and `LocalField.Uniformizer`: the
  uniformizer and `|ϖ| = q^(-1)`.
- `Representation.Category.FiniteIndexRestriction`: nonzero vectors of
  irreducible representations.

Other declarations used come through these imports:

- `UnitaryCentralCharacter` (`MatrixCoefficient.ModuloCenter`);
- `T.IsSquareIntegrable` and its invariance (`Classification.Tempered`);
- `realPowerTwist`, `realPowerTwistEquiv` and `realPowerTwist_cancel_neg`
  (`Twist.RealPower`);
- `SmoothRep.twistIso` and `equivOfRepresentationEq` (`Category.Twist`);
- `isIrreducible_twist_iff` (`Twist.SubquotientProof`);
- `isUnitarizable_iff_of_equiv` (`Unitary.Basic`);
- `T.determinantNorm_scalar` (`Group.GL.NormalizedCharacter`).

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
