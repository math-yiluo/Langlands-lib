# The VII.2.6 uniqueness assertion from named inputs

Author: Worker 4772. This is an internal reduction for proof task
`225f7d3d-bb91-4746-9084-ea6b91241e41`. It concerns the second assertion
of the Theorem of Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, VII.2.6 (printed p.231 /
PDF p.237). The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The module derives the exact published proposition
`TemperedIrreducibleDiscreteSeriesUniquenessStatement` from seven other
published propositions, which appear as explicit hypotheses. It proves none
of them, so it is not a proof of the uniqueness assertion.

## Inputs

All inputs are published `Prop` declarations, used unchanged at the
target's universes: `u` for the field, `v` for the carrier.

| Hypothesis | Published proposition | Source |
| --- | --- | --- |
| `hSq` | `SquareIntegrableNormalizedTemperedStatement.{u, v}` | VII.2.1, Remark 2 |
| `hInd` | `LeviInductionNormalizedTemperedStatement.{u, v}` | VII.2.2, Lemma |
| `hCompact` | `ArbitraryParabolicQuotientCompactStatement.{u}` | V.5.1, Corollary (compactness part) |
| `hSI` | `TemperedSquareIntegrableUnitaryPartStatement.{u, v}` | VII.2.4, Lemma |
| `hGeom` | `TemperedGeometricLemmaStatement.{u, v}` | VII.2.5, Proposition |
| `hUnimod` | `RationalPointFamily.RationalReductiveUnimodularityStatement.{u}` | unimodularity of reductive groups |
| `hStandard` | `StandardCocharacterStatement.{u}` | premise of `hUnimod` |

## Declarations

`leviInduction_isSemisimple_of_form` concerns an actual parabolic, a
rational Levi, a matching radical and the multiplication isomorphism, and a
smooth representation `σ` of `M(F)` with an `InvariantPositiveForm`. If
`(leviInductionFunctor p l r hp hr hl hmul).obj σ` is normalized-exponent
tempered, then it is a semisimple representation
(`Representation.IsSemisimpleRepresentation`). It assumes `hUnimod`,
`hStandard` and `hCompact`.

`GeometricLemmaIntersectionDatum.unitaryPieceRep_isSemisimple_of_left_full`
concerns an actual intersection datum `D` at `z` whose first intersection
parabolic `D.p' : P' ⟶ M` (Renard's `M ∩ zQz⁻¹`) is an isomorphism, and a
split component `a'` of `D.M'`. Let `σ` be a tempered representation of
`M(F)` with an invariant positive form, and let `τ` be any tempered
representation of `L(F)`. Then the literal unitary geometric piece
`D.unitaryPieceRep ha' σ` is semisimple. It assumes `hInd`, `hCompact`,
`hUnimod` and `hStandard`. The representation `τ` serves only to supply
compatible root presentations of the parabolics of `L`.

`temperedIrreducibleDiscreteSeriesUniqueness_of_inputs` proves
`TemperedIrreducibleDiscreteSeriesUniquenessStatement.{u, v}` from the seven
inputs. The entry declaration
`temperedIrreducibleDiscreteSeriesUniquenessOfInputs` is a definition whose
type is the same implication, curried in the order of the table. Its value
is this theorem.

## Proof of the uniqueness theorem

Let `π` be irreducible, with injective intertwiners into
`I₁ = i_{P₁}^G σ₁` and `I₂ = i_{P₂}^G σ₂`. Here `σ₁` and `σ₂` are irreducible
and square-integrable modulo the center for every Haar measure.

1. The quotients `M_j(F) ⧸ Z(M_j(F))` get their Borel structures and
   Mathlib's Haar measures. Then `hSq` makes `σ₁` and `σ₂` tempered and
   `hInd` makes `I₁` tempered.
2. Worker 346's `rationalSquareIntegrableUnimodularForm`, with `hUnimod`,
   gives `σ₁` an invariant positive form. By
   `leviInduction_isSemisimple_of_form`, `I₁` is semisimple.
3. Choose a split component of `M₂` (`splitComponentStatement`). Apply
   `hGeom` to the two parabolic data and `σ₁`. It gives representatives
   `z i` of the double cosets with actual intersection data `D i`, and,
   for split components `a' i` of the Levis `(D i).M'`, a filtration of
   the unitary Jacquet module `(r_{P₂}^G I₁)_0` whose graded pieces are
   isomorphic to the literal pieces `(D i).unitaryPieceRep (a' i) σ₁`. The
   split components `a' i` and `b' i` of `(D i).M'` and `(D i).L'` are
   chosen with `splitComponentStatement`.
4. The published `nonzeroUnitaryPieceMapOfInductionEmbeddings` (Renard's
   semisimplicity, tempered Frobenius reciprocity and filtration steps)
   selects an index `i` and a nonzero intertwiner from the `i`-th piece to
   `σ₂`.
5. The published `NonzeroUnitaryPieceMap.isIso_left_of_squareIntegrable`
   uses `hSI` and square-integrability of `σ₁` to show that `(D i).p'` is an
   isomorphism (Renard's `M₁ ⊂ w·P₂`).
6. `unitaryPieceRep_isSemisimple_of_left_full` makes the selected piece
   semisimple. The published
   `unitaryPieceConjugacyOfSquareIntegrableNonzeroMapFromOriginalTemperedness`
   then gives the second fullness step (Renard's `M₂ ⊂ w⁻¹·P₁`) and returns
   a `FullPieceConjugacy`. That is a scheme isomorphism `φ : M₁ ≅ M₂` with
   `φ.hom ≫ l₂ ≫ p₂ = l₁ ≫ p₁ ≫ (G.innerIso (z i)⁻¹).hom` and a linear
   equivalence `σ₁ ≃ σ₂` that intertwines `σ₁(m)` with
   `σ₂(rationalPoints.map φ.hom m)`.
7. Take `g = (z i)⁻¹`. These are exactly the conclusions of the target.

Only the selected piece has to be shown semisimple. This avoids proving
that unitary pieces with a proper first intersection vanish.

## Proofs of the semisimplicity lemmas

Both lemmas apply the published `admissibleUnitarySemisimplicity` with
compact-open cofinality from `compactOpenCofinal_of_nonarchimedean`.
Admissibility is part of normalized-exponent temperedness. The invariant
form on the induced representation is Worker 346's
`leviInductionUnimodularForm`, built from three inputs:

- ambient unimodularity from `hUnimod`;
- the compact-quotient instance from `hCompact`;
- the parabolic modulus identity `modularCharacter_of_presentation`, which
  needs Levi unimodularity and a compatible root presentation.

For `I₁`, the presentation comes from temperedness of `I₁` itself.

For the piece, write `J₀` for the unitary Jacquet module of `σ` along the
full parabolic `D.p'` and `X` for its pullback along `D.e : L'(F) ≃ M'(F)`.
Then the piece is the representation of
`(leviInductionFunctor D.q' D.lQ' D.rQ' …).obj X`.

- The published
  `unitaryPieceInducing_isNormalizedExponentTempered_of_left_full` makes
  `X` tempered on `L'`, and `hInd` (on `L`) makes the induced
  representation tempered, hence admissible.
- The published `fullParabolicUnitaryJacquetEmbedding` embeds `J₀` into `σ`
  composed with the point map of `D.l' ≫ D.p'`. Restricting (`comp`) and
  pulling back (`comap`) the form of `σ` along this embedding, and then
  restricting along `D.e`, gives a form on `X`.
- The presentation of `(D.q', D.lQ', b)` comes from temperedness of `τ` on
  `L`.

## Scope

All field, valuation, topology, local-field, connected-reductive,
local-compactness and nonarchimedean-group quantifiers of the target are
kept. Both parabolic data are arbitrary actual rational parabolics, and
square-integrability is quantified over all Haar measures. No standardness,
admissibility, finite-length, central-character, presentation-existence,
Jacquet-admissibility or Iwahori-contraction hypothesis is added beyond the
seven listed propositions. Their proofs belong to other tasks:

- `1ebce298-eeeb-4686-ba30-cabcb8e50d4b` (VII.2.1 Remark 2);
- `f83123b9-ff38-4210-9ad7-4f119a13d1ac` (VII.2.2);
- `c1ce4629-6768-4eb5-b4ee-0086526913ea` (quotient compactness);
- `f0ff1d42-b2ac-439b-a08d-8e2d120a78fa` (VII.2.4 Lemma);
- `65c3d5dc-0e10-442e-93ee-f13854e419bb` (VII.2.5).
