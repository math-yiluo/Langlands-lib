# The positive-rank Leibniz gluing from the mixed-product formulas

Author: Worker 984.

BZ77 Corollary 4.14(c) says that the `k`-th derivative of the product `ρ × σ` is glued
from the products `ρ^(j) × σ^(k-j)`. The published statement module
`Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationStatement`
indexes the pieces by the finite set `leibnizIndices a b d` and gives each index `x`
the piece functor `leibnizPiece T ψ a b d x`. Its literal source is
`leibnizSource T ψ a b d hd`, the composite of the normalized binary product, the
order-`d` general-linear derivative and forgetting smoothness.

This module proves the gluing for a first factor of positive rank `m + 1`, a second
factor of positive rank `n + 1` and a positive order `d ≤ (m + 1) + (n + 1)`. The
result is **conditional**: it takes three Prop-valued Library statements as explicit
hypotheses, namely the two halves of BZ77 4.14(a) and the proposition of BZ77
4.14(b) (see Hypotheses). The module introduces no axioms.

It is a helper unit. It does not prove the target statement
`GeneralLinearDerivativeLeibnizFiltrationStatement`. Under the task contract, a
conditional construction supplies no proof input. The theorems here bear on the
target only when a consumer discharges all three hypotheses with accepted, published
proofs, and that consumer's own audit then has to cover those proofs. The other
cases (order zero and a zero rank) are already proved without hypotheses in the
Library (see Related Library modules).

## Provenance

This content is internal to the formalization (derived). BZ77
(`bernstein-zelevinsky-1977-induced-i`, content SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`), printed p.458
(one-based PDF page 19), states Proposition 4.13 and Corollary 4.14:

- 4.13(a): for `ρ` on `G_m` and `σ` on `G_n` there is an exact sequence
  `0 → (ρ|P) × σ → (ρ × σ)|P → ρ × (σ|P) → 0` of mirabolic representations;
- 4.14(a): for `i ≥ 1`, `(ρ × τ)^(i) = ρ × τ^(i)`, where `τ` is a mirabolic
  representation;
- 4.14(b): for `i ≥ 1`, `(τ × ρ)^(i)` is glued from `τ^(j) × ρ^(i-j)`, `j = 1, …, i`;
- 4.14(c): for `i ≥ 0`, `(ρ × σ)^(i)` is glued from `ρ^(j) × σ^(i-j)`, `j = 0, …, i`.

The source proof reads: "(c) from (a), (b) and 4.13(a)". This module formalizes that
step for the actual Lean functors at positive ranks and positive order. The order-`d`
derivative is applied to the restriction sequence. The subobject term `(ρ|P) × σ`
contributes the grades `ρ^(j) × σ^(d-j)` with `j ≥ 1` by 4.14(b), since
`(ρ|P)^(j) = ρ^(j)` for `j ≥ 1` (§4.3, printed p.454, PDF p.15). The quotient term
`ρ × (σ|P)` contributes `ρ × (σ|P)^(d) = ρ^(0) × σ^(d)` by 4.14(a). This contribution
is zero when `d` exceeds the rank of `σ`. The two families are then spliced along the
exact differentiated sequence.

The differentiated sequence itself, with middle term literally `leibnizSource`, is the
published unconditional `leibnizRestrictionDerivativeExact`. That result is proved
from the published proofs of 4.13(a) and of general-linear derivative exactness. The
identification of each grade with `leibnizPiece` comes from the published
`leibnizPositivePieceIso` and `leibnizRestrictionQuotientPieceIso`. The splice and
reindexing are general filtration algebra. No errata are registered for this source in the project or the
Library. This module asserts no further original-literature theorem.

In the Library, source `P_k` (for `k ≥ 1`) is `GeneralLinear.mirabolic (k - 1)`. This
module only uses `mirabolic m` and `mirabolic n`, so no `P_0` occurs.

## Hypotheses

Each conditional theorem takes some of the following Library propositions, all at
universe levels `uF, uV`, as explicit arguments:

- `hLI : LeftMixedProductDerivativeIso F T` (BZ77 4.14(a), isomorphism half;
  `MixedProductDerivativeStatement`). Only its instance at `k = m + 1`, `r = n`,
  `i = d` with `d ≤ n + 1` is used.
- `hLV : LeftMixedProductDerivativeVanishing F T` (BZ77 4.14(a), vanishing half, with
  the source convention `τ^(i) = 0` above the rank). Only its instance at `k = m + 1`,
  `r = n`, `i = d` with `n + 1 < d` is used.
- `hRM : RightMixedProductDerivativeFiltrationStatement F T` (BZ77 4.14(b);
  `RightMixedProductDerivativeFiltrationStatement`). Only its instance at
  `k = n + 1`, `r = m`, order `d` is used.

These are statement definitions, not proofs. In the project they are owned by the
4.14(a) task `7e19f753` and the 4.14(b) task `3231134e`; neither proof is published at
this module's base. The module applies none of the conditional extractors
`.filtration` of either statement module.

## Imports

- `Langlands.Representation.Derivative.LeibnizRestrictionExact` (published, Worker
  593): the subobject `leibnizRestrictionDerivativeSubobject`, the quotient
  `leibnizRestrictionDerivativeQuotient` and the unconditional short exact sequence
  `leibnizRestrictionDerivativeExact`. Through it, the module uses `leibnizSource`,
  `leibnizPiece`, `leibnizPositivePieceIso` (`LeibnizPieceCompat`),
  `leibnizIndexSplitEquiv` (`LeibnizIndices`), `rightMixedDerivativePiece` and
  `generalLinearRepRankCast`.
- `Langlands.Representation.Derivative.LeibnizQuotientPiece` (published, Worker 984):
  `leibnizRestrictionQuotientPieceIso` and `leibnizRestrictionQuotient_subsingleton`.
- `Langlands.Representation.Derivative.MixedProductDerivativeStatement` (published
  statement module): the proposition definitions `LeftMixedProductDerivativeIso` and
  `LeftMixedProductDerivativeVanishing`, used only as hypothesis types.
- `Langlands.Representation.Filtration.GluedFamily` (published, Worker 723): the
  predicate `IsGluedFromFamily` and its laws `of_isGluedFrom`, `exists_equiv`,
  `precomp`, `isoPieces`, `equiv`, `of_iso_unique`, `of_isEmpty` and `splice`.

The module changes none of these modules or anything they import.

## Declarations

All declarations are in namespace `Langlands.Derivative`. Throughout, `F` is a
`p`-adic field with topological data `T` and `ψ` is a unitary additive character.
`IsGluedFromFamily M P`, for a finite index type `ι`, says that `M` is glued (`IsGluedFrom`) from
`P ∘ e` for some enumeration `e : Fin (card ι) ≃ ι`. `Res m` is
`generalLinearRestriction T m`, restriction from `GL_(m+1)` to `mirabolic m`. The
index split `leibnizIndexSplitEquiv m (n+1) d` sends `Sum.inl x`, for a right-mixed
index `x = (j, t)` with `j ≥ 1`, to the Leibniz index `(j, t)`. It sends the unique
element of `PLift (d ≤ n + 1)` to the zero-first index `(0, d)`.

- `isGluedFromFamily_repRankCast h hS`: for any category `C`, finite index type `ι`
  and equality `h : a = b`, if `S` is glued from `P` as functors to
  `Rep ℂ (GL_a)`, then `S ⋙ generalLinearRepRankCast h` is glued from
  `P i ⋙ generalLinearRepRankCast h`. The proof substitutes `h`.
- `leibnizRestrictionSubobjectPiece T ψ m n d x`, for
  `x : RightMixedDerivativeIndex (n+1) m d`: the definition
  `leibnizPiece T ψ (m+1) (n+1) d (leibnizIndexSplitEquiv m (n+1) d (Sum.inl x))`.
  It names the positive-first Leibniz grades, indexed like the right mixed-product
  family of 4.14(b).
- `leibnizRestrictionQuotientPiece T ψ m n d h`, for `h : PLift (d ≤ n + 1)`: the
  definition
  `leibnizPiece T ψ (m+1) (n+1) d (leibnizIndexSplitEquiv m (n+1) d (Sum.inr h))`.
  It names the zero-first Leibniz grade `(0, d)`, which exists only when
  `d ≤ n + 1`.
- `leibnizRestrictionSubobject_glued T hRM ψ m n d hd`, for
  `hd : 0 < d ∧ d ≤ (m+1)+(n+1)`: the differentiated restriction subobject
  `leibnizRestrictionDerivativeSubobject T ψ m n d hd` is glued from the family
  `leibnizRestrictionSubobjectPiece T ψ m n d` over
  `RightMixedDerivativeIndex (n+1) m d`. The proof:
  1. takes the enumeration `e` and the gluing of `rightMixedDerivativeSource
     T ψ (n+1) m d` from the pieces `rightMixedDerivativePiece T ψ (n+1) m d (e i)`,
     given by `hRM` at `k = n + 1`, `r = m`;
  2. converts it to `IsGluedFromFamily` by `of_isGluedFrom`;
  3. transports it along the output rank cast
     `((n+1)+m)+1-d = ((m+1)+(n+1))-d` by `isGluedFromFamily_repRankCast`;
  4. precomposes with `Res m × 𝟭` by `precomp`. The resulting source is
     definitionally `leibnizRestrictionDerivativeSubobject`;
  5. replaces each piece by the Leibniz piece at `leibnizPositiveIndex x` through
     `leibnizPositivePieceIso` and `isoPieces`.
- `leibnizRestrictionQuotient_glued T hLI hLV ψ m n d hd`, for
  `hd : 0 < d ∧ d ≤ (m+1)+(n+1)`: the differentiated restriction quotient
  `leibnizRestrictionDerivativeQuotient T ψ m n d hd` is glued from the family
  `leibnizRestrictionQuotientPiece T ψ m n d` over `PLift (d ≤ n + 1)`. That quotient is definitionally the composite `Q d` of
  `LeibnizQuotientPiece`. The proof splits cases:
  - if `d ≤ n + 1`, the index type has exactly one element. `of_iso_unique` applies
    to `leibnizRestrictionQuotientPieceIso T ψ m n d ⟨hd.1, _⟩ E`, where `E` is the
    isomorphism chosen (`Classical.choice`) from the `Nonempty` conclusion of
    `hLI ψ (m+1) n d`;
  - if `n + 1 < d`, the index type is empty. `of_isEmpty` applies to
    `leibnizRestrictionQuotient_subsingleton T ψ m n d hd V`, where `V` is
    `hLV ψ (m+1) n d _ _`.
- `leibnizSource_glued_pos T hLI hLV hRM ψ m n d hd`, for
  `hd : 0 < d ∧ d ≤ (m+1)+(n+1)`: `leibnizSource T ψ (m+1) (n+1) d hd.2` is glued
  from the full family `leibnizPiece T ψ (m+1) (n+1) d` over
  `LeibnizIndex (m+1) (n+1) d`. The proof takes the natural maps `i`, `q` and their
  objectwise injectivity, exactness and surjectivity from
  `leibnizRestrictionDerivativeExact T ψ m n d hd`. It splices the two families
  above along them (`splice`), which gives gluing from their `Sum.elim`. Then it
  reindexes along `leibnizIndexSplitEquiv m (n+1) d` (`equiv`). By the two piece
  definitions above, each piece of the `Sum.elim` is definitionally the Leibniz piece
  at the image index, so every piece isomorphism is `Iso.refl`.
- `generalLinearDerivativeLeibnizFiltration_pos T hLI hLV hRM ψ m n d hd`, for
  `hd : 0 < d ∧ d ≤ (m+1)+(n+1)`: there are an equivalence
  `e : LeibnizIndex (m+1) (n+1) d ≃ Fin (leibnizIndices (m+1) (n+1) d).card` and a
  gluing `IsGluedFrom (leibnizSource T ψ (m+1) (n+1) d hd.2) (fun i => leibnizPiece
  T ψ (m+1) (n+1) d (e.symm i))`. This is exactly the body of the target statement
  at `a = m + 1`, `b = n + 1` and order `d`. By proof irrelevance, any proof of
  `d ≤ (m+1)+(n+1)` may stand for `hd.2`. The proof applies `exists_equiv` to the
  previous theorem, with `Fintype.card_coe`.

The pieces are the unchanged `leibnizPiece` values at all feasible indices, including
indices whose piece is zero. Nothing is assumed of the carriers, which lie in universe
`uV`, or of `ψ`. The top order `d = (m+1)+(n+1)` is included; there the quotient
family is empty. The largest zero-first order `d = n + 1` is also included; there the
derivative of the second factor is a representation of `GL_0`.

All declarations use universe levels `uF` (field) and `uV` (carriers of the factors),
as in the statement module. The checked axioms of
`generalLinearDerivativeLeibnizFiltration_pos`, `leibnizRestrictionSubobjectPiece` and
`leibnizRestrictionQuotientPiece` are `propext`, `Classical.choice` and `Quot.sound`.

## Import closure and dependency audit

At Library base `8f53f05bb76983088fd64f190658c6ac4c3edc1b`, a recursive scan of the
`import Langlands.…` lines gives exactly these 190 modules in the transitive project
closure, not counting this module. Each has a nonempty paired Markdown file, and
each is byte-identical to the published base:

- `Langlands.Analysis`: `Local.ModularCompactAverage`, `Local.QuotientMeasure`, `Local.QuotientTopology`.
- `Langlands.Group`: `GL.Basic`, `GL.BlockModulus`, `GL.Blocks`, `GL.CompactOpen`, `GL.CountabilityProof`, `GL.CountabilityStatement`, `GL.Maps`, `GL.Mirabolic`, `GL.MirabolicMixedProductSubgroups`, `GL.MirabolicModularCharacterProof`, `GL.MirabolicModularCharacterStatement`, `GL.MirabolicModulusProof`, `GL.MirabolicModulusStatement`, `GL.MirabolicOppositeIntersection`, `GL.MirabolicProjection`, `GL.MirabolicRadical`, `GL.Nonarchimedean`, `GL.NonarchimedeanStatement`, `GL.NormalizedCharacter`, `GL.OppositeBlocks`, `GL.Padic`, `GL.PadicBlocks`, `GL.PadicOppositeBlocks`, `GL.PadicUpperUnipotent`, `GL.RankMaps`, `GL.RankReindex`, `GL.TriangularParabolic`, `GL.UpperUnipotent`, `GL.UpperUnipotentCompactContainmentProof`, `GL.UpperUnipotentCompactContainmentStatement`, `HaarModulus`.
- `Langlands.HarmonicAnalysis`: `Basic`, `Conductor`, `PadicAdditiveConductorProof`, `PadicHaarScalingStatement`, `PadicLatticeTopology`, `PadicRectangularHaarScalingProof`, `PadicScalarHaarScalingProof`.
- `Langlands.LocalFactor`: `Harmonic.Statement`.
- `Langlands.LocalField`: `Canonical`, `Definitions`, `Normalization.Definitions`, `Normalization.Proof`, `Normalization.Statement`, `Topology`.
- `Langlands.Representation`: `OrbitSpan`.
- `Langlands.Representation.Category`: `Basic`, `Subquotients`, `Twist`.
- `Langlands.Representation.Classification`: `Supercuspidal`, `SupercuspidalContragredientAux`, `SupercuspidalContragredientStatement`.
- `Langlands.Representation.Compact`: `Definitions`, `FiniteMean`, `OrbitMeanTranslation`, `ProjectionProof`, `ProjectionStatement`.
- `Langlands.Representation.Conductor`: `Congruence`.
- `Langlands.Representation.Derivative`: `GeneralLinearDerivativeExactnessProof`, `GeneralLinearDerivativeExactnessStatement`, `GeneralLinearDerivativeLeibnizFiltrationStatement`, `Homogeneity`, `Iteration`, `LeibnizIndices`, `LeibnizPieceCompat`, `LeibnizQuotientPiece`, `LeibnizRestrictionCompat`, `LeibnizRestrictionExact`, `LeibnizZeroFirstPiece`, `MinusVanishing`, `MirabolicCharacter`, `MirabolicLatticeBox`, `MirabolicMinus`, `MirabolicMinusExactnessProof`, `MirabolicMinusExactnessStatement`, `MirabolicProductRestriction`, `MirabolicProductRestrictionCasts`, `MirabolicProductRestrictionFactors`, `MirabolicProductRestrictionMackey`, `MirabolicProductRestrictionOrbits`, `MirabolicProductRestrictionStabilizers`, `MirabolicProductRestrictionStatement`, `MirabolicProductRestrictionTransport`, `MixedProductDerivativeStatement`, `RankCastCompat`, `RightMixedProductDerivativeFiltrationStatement`, `ShortExactFunctorLaws`.
- `Langlands.Representation.Dual`: `Definitions`.
- `Langlands.Representation.Filtration`: `Definitions`, `GluedFamily`, `IsoTransport`, `OneStep`, `Precomposition`, `QuotientFirstIso`, `QuotientTail`, `Splicing`, `Splicing.Basic`, `Transport`.
- `Langlands.Representation.Geometric`: `ClosedSubgroupAssembly`, `ClosedSubgroupDefinitions`, `ClosedSubgroupMackeyProof`, `ClosedSubgroupStatement`, `CompactOrbitRestriction`, `CosetAction`, `CosetOrbitHomeomorph`, `OrbitRestriction`, `OrbitSectionExtensionProof`, `OrbitSectionExtensionStatement`.
- `Langlands.Representation.Induction`: `BinaryProduct`, `BlockFactors`, `CompactLocalSection`, `CompactQuotientCutoff`, `CompactQuotientProof`, `Definitions`, `Parabolic`, `StructuralStatement`.
- `Langlands.Representation.Jacquet`: `CharacterAveraging`, `Coinvariants`, `ExactProof`, `ExactStatement`, `Localization`, `LocalizationExactnessProof`, `LocalizationExactnessStatement`, `PositiveCharacter`, `SmoothTwist`.
- `Langlands.Representation.MatrixCoefficient`: `Definitions`, `LawsProof`, `LawsStatement`.
- `Langlands.Representation.Mirabolic`: `MixedProducts`.
- `Langlands.Representation.Parabolic`: `GeometricPrerequisitesStatement`, `QuotientCompactProof`.
- `Langlands.Representation.RankinSelberg`: `GeneralLinearUnimodularity`, `LastRowCompactOrbitProof`, `LastRowCompactOrbitStatement`, `Measures`, `QuotientIntegrals`, `UnimodularityStatement`, `UnipotentUnimodularity`, `ZeroRowLastRowCutoffProof`, `ZeroRowLastRowCutoffStatement`.
- `Langlands.Representation.Smooth`: `Admissibility.CofinalProof`, `Admissibility.CofinalStatement`, `Admissibility.EquivalenceProof`, `Admissibility.EquivalenceStatement`, `Contragredient.CompactDualityProof`, `Contragredient.CompactDualityStatement`, `Contragredient.Definitions`, `Contragredient.FixedVectorsDefinitions`, `Contragredient.LawsProof`, `Contragredient.LawsStatement`, `Definitions`, `FixedVectors.Definitions`, `SmallRealizationProof`, `SmallRealizationStatement`, `SmoothPart.BasicProof`, `SmoothPart.BasicStatement`, `SmoothPart.Definitions`, `SmoothPart.FixedVectorsDefinitions`, `Transfer.PullbackProof`, `Transfer.PullbackStatement`, `Transfer.SubquotientProof`, `Transfer.SubquotientStatement`.
- `Langlands.Representation.Tensor`: `Finite`, `FiniteEquivalences`, `OneFactor`.
- `Langlands.Representation.Twist`: `AdmissibilityProof`, `AdmissibilityStatement`, `AlgebraProof`, `AlgebraStatement`, `ContinuousCharacterProof`, `ContinuousCharacterStatement`, `Definitions`, `RealPower`, `SmoothProof`, `SmoothStatement`, `SubquotientDefinitions`, `SubquotientProof`, `SubquotientStatement`.
- `Langlands.Representation.Unitary`: `Basic`.
- `Langlands.Representation.Whittaker`: `Algebraic`, `GeneralLinear`, `Iwasawa`.
- `Langlands.Topology`: `CompactNormCharacter`, `CompactOpen.ConjugationStabilizer`, `CompactOpen.NeighborhoodBasis`, `CompactOpen.NeighborhoodBasisStatement`, `Nonarchimedean.Subgroup`.

These are the 179 modules of the published `LeibnizRestrictionExact` closure
(including that module), together with `LeibnizQuotientPiece`, `LeibnizZeroFirstPiece`,
`MixedProductDerivativeStatement` and the eight filtration modules `GluedFamily`,
`IsoTransport`, `OneStep`, `Precomposition`, `QuotientTail`, `Splicing`,
`Splicing.Basic` and `Transport`.

A text scan of every Lean file in the closure was run for all task identifiers named in
the task contract and for the excluded declaration names it names. These include
`SupercuspidalCoinvariantFinitenessStatement`,
`IrreducibleCoinvariantFinitenessStatement`, `LeviCuspidalCoinvariantFinitenessStatement`,
`SquareIntegrableLanglandsClassification`, `GenericSegmentProductUniqueness`,
`SegmentHeadProductIrreducibility`, `SegmentSocleProductIrreducibility`,
`TwoSupercuspidalNonadjacentProductIrreducible`, `TwoSupercuspidalProductStructure` and
the segment-socle, segment-Jacquet and exhaustion statements. It finds none of them.
The only name matches are the target statement module itself and `LeibnizIndices`,
which imports the target module to name the index set. The target's
`.filtration` extractor is not used. A case-insensitive scan finds no Lean file in the
closure that mentions segments or socles. The words "classification" and
"supercuspidal" occur only in the three `Classification` modules and in
`Smooth.SmallRealizationProof`. The only finite-length mention is the definition
`HasFiniteLength` in `Representation.Category.Basic`, which this module does not use.

The three modules `Classification.Supercuspidal`,
`Classification.SupercuspidalContragredientStatement` and
`Classification.SupercuspidalContragredientAux` enter only through the published proof
of 4.13(a), via `MirabolicProductRestrictionMackey` → `Group.GL.CountabilityProof` →
`Smooth.SmallRealizationProof`. They define the supercuspidal predicate, state a
contragredient proposition and prove elementary dual, coinvariant-conjugation and
equivalence lemmas. As documented in `LeibnizRestrictionExact`, the restriction proof
uses from this chain only the second-countability certificate for `GL_n(F)`, which
is proved from finite matrix products. This module itself uses no declaration from
these modules.

The mathematical inputs of the proofs, condition by condition:

- **Restriction sequence and exactness.** `leibnizRestrictionDerivativeExact` is
  unconditional and published. Its Markdown traces it to the published proofs of
  BZ77 4.13(a) (`MirabolicProductRestriction`) and of general-linear derivative
  exactness (`GeneralLinearDerivativeExactnessProof`, which uses the published
  mirabolic minus exactness). No exactness proposition is assumed.
- **Piece identifications.** `leibnizPositivePieceIso` (`LeibnizPieceCompat`) and
  `leibnizRestrictionQuotientPieceIso` and `leibnizRestrictionQuotient_subsingleton`
  (`LeibnizQuotientPiece`) are unconditional constructions from explicit data. Here
  that data is instantiated from `hLI` and `hLV`.
- **Filtration algebra.** The `IsGluedFromFamily` laws, the rank-cast transport
  (equality elimination) and `leibnizIndexSplitEquiv` are general finite reindexing,
  splicing and precomposition facts with no representation-theoretic premise.
- **4.14(a) and 4.14(b).** These are supplied only by the hypotheses `hLI`, `hLV` and
  `hRM`. They are not proved here and are not imported as proofs.

Against the inherited exclusions of the task contract:

| Inherited condition or exclusion | Check for this module |
| --- | --- |
| Actual functors, unchanged target and imported pairs, complete feasible indices, smooth casts, no residual twist | The source is literally `leibnizSource` and the pieces are the unchanged `leibnizPiece` at every feasible index, including zero pieces. The enumeration comes from `exists_equiv`. No Library pair is edited. |
| Supplied `T`, `ψ`, independent universes `uF`, `uV`, arbitrary carriers, boundaries | These are unchanged parameters with no representation hypothesis. Positive ranks and positive order are the explicit scope. The top and zero-first top orders are covered. The order-zero and zero-rank cases are separate published results. |
| Only accepted, published general inputs; no proposition, citation, draft, pending task or conditional construction as a proof input | Every Lean input is published at the base. 4.14(a) and 4.14(b) enter only as explicit Prop-valued hypotheses, and this module is itself a conditional construction. So it supplies no proof of the target until the hypotheses are discharged by accepted, published proofs whose closures are audited separately. |
| Segment derivative formulas, segment-socle/head existence, full/head/socle Jacquet and special-exponent formulas, analytic segment classification | No segment module or declaration is in the closure or in the proof route. |
| Unlinked/linked/juxtaposed socle structures, pair reducibility, reverse quotient maps, socle product irreducibility, adjacent swaps, two-segment commutation, linked gluing, ordered socle existence, socle exhaustion | None occurs in the closure or the proof route. |
| Special-head criterion, generic segment-product uniqueness, multisegment exhaustion, ordered strong-head existence, quotient coverage, ordered conversion, tempered uniqueness | None occurs. The incidental `Classification` imports above prove no such conclusion and are not used. |
| Square-integrable classification, square-integrable and regular exhaustion, forward special square-integrability | No square-integrable or exhaustion theorem is imported or used. |
| Two-supercuspidal irreducibility, product structure or assembly | None occurs in the closure or the proof route. |
| Ze80 segment derivatives (§3.5, §9.6), criteria 4.2/9.7, 9.3 analytic results | No Ze80 result is used. The route is BZ77 4.14(c) from (a), (b) and 4.13(a). |
| Irreducible, Levi-cuspidal, supercuspidal and all-character single-block Whittaker coinvariant finiteness; the dependent mirabolic finite-length route | None of these declarations or tasks occurs in the closure. No finite-length, admissibility or irreducibility theorem is used. |
| Worker 127 operator pause; ownership | No contact with Worker 127. This module does not prove 4.14(a) or 4.14(b) or claim the final theorem, which Worker 593 integrates. |

This scan supplements the mathematical trace above; it does not replace independent
review.

## Related Library modules

The published `GeneralLinearDerivativeLeibnizBoundary` (Worker 593) proves the order-zero
case `generalLinearDerivativeLeibnizFiltration_zero`. `LeibnizRankZeroGluing`
(Worker 593, using Worker 984's `LeibnizRankZeroBoundary`) proves the cases where the
first or the second rank is zero. Both prove them without hypotheses. Together with
this module, those cases cover every `a`, `b`, `d` with `d ≤ a + b`, once 4.14(a) and
4.14(b) are proved. The published `RightMixedProductDerivativePositive` (Worker 723,
with Markdown revisions by Worker 969) proves 4.14(b) at positive `GL` rank
conditionally, from hypotheses that include `hLI` and `hLV`. Worker 969's
`RightMixedProductZeroRank` proves its `GL_0` case. This module imports neither and
takes 4.14(b) only through `hRM`.
