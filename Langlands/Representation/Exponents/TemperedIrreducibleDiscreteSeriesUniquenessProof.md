# Proof of the VII.2.6 uniqueness assertion

Author: Worker 4772, for proof task `225f7d3d-bb91-4746-9084-ea6b91241e41`.
The module proves the published proposition
`Langlands.Aubert.General.RepresentedParabolic.TemperedIrreducibleDiscreteSeriesUniquenessStatement`.
This is the second assertion of the Theorem of Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, VII.2.6 (printed p.231 /
PDF p.237). The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The target is stated at universes `u` (field) and `v` (carrier). Let `π` be an
irreducible smooth representation of `G(F)`, and suppose `π` embeds into
`i_{P₁}^G σ₁` and into `i_{P₂}^G σ₂`. Here each `σ_j` is an irreducible
representation of the rational Levi `M_j(F)` of an actual parabolic `P_j`, and it is
square-integrable modulo the center for every Haar measure. Then there are
`g ∈ G(F)`, a scheme isomorphism `φ : M₁ ≅ M₂` with
`φ.hom ≫ l₂ ≫ p₂ = l₁ ≫ p₁ ≫ (G.innerIso g).hom`, and a linear equivalence
`σ₁ ≃ σ₂` intertwining `σ₁(m)` with `σ₂(φ(m))`.

## Relation to the published reduction

The published `temperedIrreducibleDiscreteSeriesUniqueness_of_inputs`
(`TemperedIrreducibleDiscreteSeriesUniquenessReduction.lean`) derives the target from
seven published propositions. Six of them now have published proofs, which this
module imports:

| Input | Published proof |
| --- | --- |
| VII.2.1 Remark 2, `SquareIntegrableNormalizedTemperedStatement` | `squareIntegrableNormalizedTempered` (Worker 4713) |
| VII.2.2, `LeviInductionNormalizedTemperedStatement` | `leviInductionNormalizedTempered` |
| quotient compactness, `ArbitraryParabolicQuotientCompactStatement` | `arbitraryParabolicQuotientCompact` |
| VII.2.5, `TemperedGeometricLemmaStatement` | `temperedGeometricLemma` |
| unimodularity, `RationalPointFamily.RationalReductiveUnimodularityStatement` | `RationalPointFamily.rationalReductiveUnimodularity` |
| `StandardCocharacterStatement` | `standardCocharacter` |

The seventh input, the VII.2.4 Lemma `TemperedSquareIntegrableUnitaryPartStatement`,
is an equivalence. Its proof is open (task `f0ff1d42-b2ac-439b-a08d-8e2d120a78fa`).
Its reverse direction needs the sufficiency half of Casselman's criterion. The
reduction uses only its forward direction, in two places:
`NonzeroUnitaryPieceMap.isIso_left_of_squareIntegrable` (`ActualUnitaryPieceFullness.lean`)
and `isIso_of_squareIntegrable_semisimple_induction_quotient`
(`TemperedInductionQuotientNonvanishing.lean`). Renard's proof uses the same direction
too: a nonzero `(r^{M₁}_{M₁∩w·P₂} E₁)₀` forces `M₁ ∩ w·P₂ = M₁`, and similarly for
`M₂`. This module proves that direction, without temperedness or central-character
hypotheses, as `squareIntegrable_unitaryJacquetPart_eq_bot`. It then repeats the two
fullness steps and the conjugacy assembly with that theorem in place of the VII.2.4
input.

## Declarations

### `squareIntegrable_unitaryJacquetPart_eq_bot`

Take a connected reductive `G` over a nonarchimedean local field, with the published
point topology, local compactness and the nonarchimedean group instance. Take any Borel
measurable structure on `G(F) ⧸ Z(G(F))` and any Haar measure `haar` on it. Let `π` be
a smooth representation in any carrier universe `v` with
`IsSquareIntegrableModCenter π.representation haar`. Then
`unitaryJacquetPart p l r hp hl hr hmul ha π = ⊥` for every actual parabolic `p` with
`¬ IsIso p`, every rational Levi `l`, matching geometric unipotent radical `r` with
multiplication isomorphism `hmul`, and every split component `a` of the Levi. The
binders match those of the forward direction of `TemperedSquareIntegrableUnitaryPartStatement`.
That statement also assumes temperedness and a central character; this theorem does not.

Proof. The published `parabolicRootPresentationExistence` gives a
`ParabolicRootPresentation p l a`. The published `arbitraryParabolicCasselmanNecessity`
(Worker 4712) puts the real part of every normalized Jacquet exponent of `π` in the
strictly positive cone of that presentation. The published
`unitaryJacquetPart_eq_bot_of_positive_exponents` concludes. It uses
`unitaryJacquetPart_eq_bot_iff`, and the fact that `0` is not in the strictly positive
cone of a proper parabolic. This follows Renard's proof of the VII.2.4 Lemma (printed
p.230 / PDF p.236): "des définitions … et du critère de Casselman". Casselman's
criterion is used only in its necessity direction.

### `isIso_of_squareIntegrable_semisimple_induction_quotient_of_necessity`

Take an actual parabolic datum `(p, l, r, hmul)` of `G`, a split component `a`, a
tempered `σ` of `M(F)` whose induction is semisimple, and an irreducible tempered `π`
of `G(F)` that is square-integrable modulo the center for some Haar measure. If there
is a nonzero intertwiner from `i_P^G σ` to `π`, then `p` is an isomorphism. The
published `unitaryJacquetPart_ne_bot_of_semisimple_induction_quotient` makes the unitary
Jacquet part of `π` along `p` nonzero. If `p` were proper,
`squareIntegrable_unitaryJacquetPart_eq_bot` would make it zero. This repeats the
published `isIso_of_squareIntegrable_semisimple_induction_quotient` without its VII.2.4
argument.

### `GeometricLemmaIntersectionDatum.NonzeroUnitaryPieceMap.isIso_left_of_squareIntegrable_of_necessity`

Take an actual intersection datum `D` at `z`, a split component `a'` of `D.M'`, a
representation `σ` of `M(F)` that is square-integrable modulo the center for `haarM`,
and a nonzero map `F` from the literal unitary piece of `σ` to some representation `τ`
of `L(F)`. Then the first intersection parabolic `D.p'` (Renard's `M ∩ w·Q`) is an
isomorphism. The published `NonzeroUnitaryPieceMap.unitaryJacquetPart_ne_bot` makes the
unitary Jacquet part of `σ` along `D.p'` nonzero. Then
`squareIntegrable_unitaryJacquetPart_eq_bot` on `M` excludes a proper `D.p'`. The
published version also needed temperedness of `σ` and the VII.2.4 input; this one
needs neither.

### `GeometricLemmaIntersectionDatum.NonzeroUnitaryPieceMap.isIso_right_of_squareIntegrable_of_necessity`

In the same setting, assume also:

- `τ` is irreducible, tempered and square-integrable modulo the center for `haarL`;
- the unitary piece is semisimple;
- the inner inducing module, the pullback along `D.e` of the unitary Jacquet module of
  `σ` along `D.p'`, is tempered on `D.L'`.

Then the second intersection parabolic `D.q'` (Renard's `L ∩ w⁻¹·P`) is an isomorphism.
The proof applies `isIso_of_squareIntegrable_semisimple_induction_quotient_of_necessity`
on `L` to the induction from `D.q'` of that inducing module and the map `F`.

### `GeometricLemmaIntersectionDatum.unitaryPieceConjugacyOfSquareIntegrableNonzeroMapOfNecessity`

Assume the hypotheses of both fullness steps, except temperedness of the inducing
module, and add irreducibility of `σ` and `τ`. The result is a `FullPieceConjugacy`: a
scheme isomorphism `M ≅ L` with `leviIso.hom ≫ lQ ≫ q = l ≫ p ≫ (G.innerIso z⁻¹).hom`,
and a linear equivalence `σ ≃ τ` that intertwines `σ` with `τ` composed with
`leviIso`. The proof:

1. First fullness makes `D.p'` an isomorphism.
2. The published
   `unitaryPieceInducing_isNormalizedExponentTempered_of_left_full` then makes the
   inducing module tempered.
3. Second fullness makes `D.q'` an isomorphism.
4. The published `unitaryFullPieceConjugacyOfNonzeroMap` gives the conjugacy.

This repeats the published
`unitaryPieceConjugacyOfSquareIntegrableNonzeroMapFromOriginalTemperedness` without its
two VII.2.4 arguments.

### `temperedIrreducibleDiscreteSeriesUniqueness_of_squareIntegrableTempered`

The target, assuming only `SquareIntegrableNormalizedTemperedStatement.{u, v}`. The
proof follows `temperedIrreducibleDiscreteSeriesUniqueness_of_inputs` step by step. It
takes the other five inputs from their published proofs and uses the theorems of this
module for the two fullness steps:

1. Give `M_j(F) ⧸ Z(M_j(F))` its Borel structure and Mathlib's Haar measure `haar_j`.
   By hypothesis, `σ₁` and `σ₂` are tempered. `leviInductionNormalizedTempered` makes
   `I₁ = i_{P₁}^G σ₁` tempered.
2. `rationalSquareIntegrableUnimodularForm` and unimodularity give `σ₁` an invariant
   positive form. The published `leviInduction_isSemisimple_of_form` then makes `I₁`
   semisimple.
3. Choose a split component of `M₂`. `temperedGeometricLemma` gives the double-coset
   representatives `z i`, the intersection data `D i`, and the filtration of the unitary
   Jacquet module of `I₁` along `P₂` by the literal unitary pieces. Choose split
   components `a' i` of `(D i).M'` and `b' i` of `(D i).L'`.
4. The published `nonzeroUnitaryPieceMapOfInductionEmbeddings` selects an index `i`
   and a nonzero map `F` from the `i`-th unitary piece to `σ₂`.
5. `isIso_left_of_squareIntegrable_of_necessity` makes `(D i).p'` an isomorphism. The
   published `unitaryPieceRep_isSemisimple_of_left_full` then makes the piece
   semisimple.
6. `unitaryPieceConjugacyOfSquareIntegrableNonzeroMapOfNecessity` returns the
   conjugacy. With `g = (z i)⁻¹` its fields are the conclusions of the target.

### `temperedIrreducibleDiscreteSeriesUniqueness`

The entry theorem, of type exactly
`TemperedIrreducibleDiscreteSeriesUniquenessStatement.{u, v}`. It applies the previous
theorem to Worker 4713's published `squareIntegrableNormalizedTempered`.

## Scope

The target's binders are introduced unchanged. These are:

- every field, valuation, topology, local-field and connected-reductive quantifier;
- the local-compactness and nonarchimedean-group instances;
- the arbitrary field and carrier universes;
- two arbitrary actual parabolic, rational Levi and radical data;
- square-integrability over all Haar measures.

The proof adds no standardness, admissibility, finite-length, central-character,
presentation-existence, Jacquet-admissibility, quotient-compactness or
Iwahori-contraction premise. Where the source assumes `P₁` and `P₂` standard and takes
`w` in `W_{M₂,M₁}`, the proof uses the double-coset representatives `z i` and actual
intersection data of the published tempered geometric lemma. Its `g = (z i)⁻¹`
conjugates `M₁` onto `M₂` as maps into `G`.
