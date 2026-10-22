# Standalone and common-closure reciprocity transport

Author: Worker 100. This is a derived comparison construction with its intrinsic
transport and normalization laws. It imports the published field and units
comparison of Worker 28 in `ExtensionFieldTransport`; it does not duplicate it.

## Inputs and actual objects

Fix a prime `p`, `F : PadicField.{u} p`, `E : PadicField.{v} p`, and an actual
algebra homomorphism `f : F.Carrier →ₐ[Padic p] E.Carrier`. The field universes
`u` and `v` are independent. Let `J = extensionFiniteIntermediate F E f`.
Its field is precisely `extensionIntermediateField F E f`, the image of the
existing choice-based algebraic-closure lift. Its finiteness certificate and
canonical topological data are the published constructions, not extra inputs.
Write `H` for `pullbackFixingSubgroup F.Carrier J.field (localResidueDegree F)`.

`extensionWeilRange_eq_fixing` identifies the published Weil-map range with
`H`, using `extensionWeilMap_range` and `extensionGaloisMap_range`.
`extensionImageWeilEquiv` composes `extensionWeilRangeEquiv` with the
subgroup equality. Thus it is a topological group equivalence `W_E ≃ₜ* H`.
The equality identification is continuous in both directions because it
preserves the underlying element of `W_F` and both topologies are subspace
topologies. `extensionImageWeilEquiv_apply` gives its actual inclusion:

`(extensionImageWeilEquiv F E f w : W_F) = extensionWeilMap F E f w`.

`extensionImageAbelianEquiv` applies `abelianizationCongr` to that equivalence.
It identifies the actual quotients by the closed commutator subgroups, with
their quotient topologies. `extensionImageAbelianEquiv_projection` gives the
corresponding identity on quotient generators.

## Degree and norm compatibility

Put `r = extensionResidueDegree F E f`. The common-closure degree uses the
base field `F`. `extensionImageWeilEquiv_degree` states that the integer
degree of the included element is `r * deg_E(w)`.
`extensionImageAbelianEquiv_degree` states the same law after abelianization:

`J.weilDegree (localResidueDegree F) (extensionImageAbelianEquiv F E f x)
 = (WeilQuotients.degree (localResidueDegree E) x) ^ r`.

Here degree takes values in `Multiplicative ℤ`, so the natural-number power
expresses multiplication of the corresponding integer by `r`. The quotient
proof uses quotient induction and the published degree formula for the actual
Weil map. `extensionImageWeilEquiv_normCharacter` states that `localNormCharacter F`
on the included element equals `localNormCharacter E` on the original element.
It specializes the published norm-character compatibility of `extensionWeilMap`.

## Conditional candidate and characters

Supply `e : CommonClosure.CandidateFamily F (CommonClosure.canonicalData F)
(localResidueDegree F)`. No such family is selected or proved to exist.
Let `A = extensionImageAbelianEquiv F E f`, `U = extensionIntermediateUnitsEquiv F E f`,
and `e_J = e J`. The construction is the continuous multiplicative equivalence

`extensionReciprocityCandidate F E f e = U.symm ∘ e_J ∘ A`.

Its type is exactly `WeilReciprocityCandidate E.canonicalTopologicalData
(localResidueDegree E)`. The topology on `E` and the image field is their
canonical topology throughout. Although the API accepts a family, the
construction uses only its component at `J`.
`extensionReciprocityCandidate_projection` gives the formula on every quotient
generator, using the actual Weil comparison and the actual inverse units map.

`extensionReciprocityCandidate_character` compares the two routes for a
continuous complex character `χ : H →ₜ* ℂˣ` and a unit `a : E.Carrierˣ`.
Transporting `χ` after precomposition with `extensionImageWeilEquiv` through
the constructed standalone candidate equals transporting `abelianizationLift χ`
through `e_J` and evaluating at `U a`. The proof uses
`abelianizationLift_comp_equiv`, followed by cancellation of `A` with its inverse.
It imposes no unitarity, finite-order, or unramifiedness condition on `χ`.

`extensionReciprocityCandidate_character_projection` says that for every
continuous complex character of `W_E`, evaluation of its transported character
at the candidate image of the class of `w` is exactly its original value at
`w`. This follows by cancelling the candidate with its inverse, then evaluating
the descended character on a quotient generator.

## Geometric normalization

The last three theorems additionally assume precisely
`CommonClosure.NormalizationRelation F (CommonClosure.canonicalData F)
(localResidueDegree F) F.canonicalTopologicalData e`. They need no coherence,
density, completion, norm, or transfer relation.

`extensionReciprocityCandidate_normalizedAbs` proves, for every element `x` of
the standalone Weil abelianization,

`|extensionReciprocityCandidate F E f e x|_E = q_E ^ (-deg_E(x))`.

The implemented proof first uses
`extensionIntermediateUnitsEquiv_symm_normalizedAbs` to move to the actual image
field. The supplied normalization gives `q_F ^ (-deg_F(A x))`. The constructed
quotient degree formula gives `deg_F(A x) = r * deg_E(x)`, and the published
`extensionResidueCardinality F E f` gives `q_E = q_F ^ r`. Integer-power laws
and an integer arithmetic identity then yield the displayed formula.

`extensionReciprocityCandidate_geometricOrder` proves the published predicate
`GeometricOrderRelation` for this candidate: order after the candidate equals
the descended geometric degree, with the plus sign. The proof rewrites the
normalized absolute value of a unit as `q_E ^ (-ord_E(a))` and uses `q_E > 1`
to inject the integer exponent, then cancels the two negative signs.

`extensionReciprocityCandidate_normCharacter` proves, for every unit `a`, that
the transported actual `localNormCharacter E`, viewed in `ℂ`, is the real
normalized absolute value of `a` embedded in `ℂ`. The proof uses surjectivity
of the constructed candidate, quotient induction, the character generator
formula, the preceding absolute-value identity, and `residueNormCharacter_apply`.

## Derived provenance and source locations

This module derives the comparison directly from published Library declarations.
It invokes no new literature theorem or additional compatibility assumption.
The exact internal sources are:

- `Langlands/Weil/Local/ExtensionGalois.lean`, `extensionGaloisMap_range`
  (line 187), together with its actual image field. `ExtensionFieldTransport.lean`,
  `extensionFiniteIntermediate` (line 25), packages that field's finiteness.
- `Langlands/Weil/Local/ExtensionWeil.lean`, `extensionWeilMap_range` (line 465),
  `localDegree_extensionWeilMap` (line 351), `localDegreeInt_extensionWeilMap`
  (line 355), and `localNormCharacter_extensionWeilMap` (line 377).
- `Langlands/Weil/Local/ExtensionWeilRange.lean`, `extensionWeilRangeEquiv`
  (line 21), for the topological range identification.
- `Langlands/LocalClassField/AbelianizationTransport.lean`, `abelianizationCongr`
  (line 58) and `abelianizationLift_comp_equiv` (line 120), for the quotient
  equivalence and character naturality.
- `Langlands/ClassFieldTheory/Local/ExtensionFieldTransport.lean`,
  `extensionIntermediateUnitsEquiv` (line 75) and
  `extensionIntermediateUnitsEquiv_symm_normalizedAbs` (line 111), for the
  actual units equivalence and its normalization identity.
- `Langlands/ClassFieldTheory/Local/ReciprocitySystem.lean`, `weilDegree`,
  `CommonClosure.CandidateFamily`, `CommonClosure.NormalizationRelation`, and
  `CommonClosure.canonicalData`, for the exact family and its condition.
- `Langlands/ClassFieldTheory/Local/ReciprocityRelations.lean`,
  `WeilReciprocityCandidate`, `GeometricOrderRelation`, and
  `weilCandidateCharacterEquiv`; `FiniteArtin.lean`, `characterTransport`;
  `WeilAbelianization.lean`, `projection`, `degree`, and `characterDescent`.
- `Langlands/Weil/Local/ExtensionResidue.lean`, `extensionResidueCardinality`
  (line 136); `Langlands/LocalField/Normalization/Proof.lean`,
  `residueCardinality_gt_one` and `normalizedAbs_of_ne_zero`; and
  `Langlands/Weil/Local/ResidueCharacters.lean`, `residueNormCharacter_apply`.

The paired Markdown of these published modules records their inherited
mathematical provenance. The comparison here is an internal composition of
those actual maps and their proved identities. Mathlib supplies subgroup
congruence, quotient induction, inverse cancellation, and `zpow_right_injective₀`.

## Scope

The result constructs a candidate from an explicitly supplied family and
transports its geometric normalization and complex characters. It does not
assert the standalone `LocalReciprocityCandidateRelation`, its finite
norm-residue or density conditions, or `GeometricWeilReciprocityRelation`.
It supplies no reciprocity existence or uniqueness theorem and no epsilon
system. All comparisons retain the choices in the existing closure lift;
identity/composition coherence and independence of those choices are not
asserted. The public field helper remains a separate imported construction.
