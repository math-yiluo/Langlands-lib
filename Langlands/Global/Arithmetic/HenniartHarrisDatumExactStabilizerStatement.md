# Henniart's datum characters under the exact Weil stabilizer condition

Module `Langlands.Global.Arithmetic.HenniartHarrisDatumExactStabilizerStatement`,
namespace `Langlands.Global`. It imports
`HenniartHarrisDatumStatement` and
`HarrisProposition48ExactStabilizerData`, which defines
`Harris.IsProposition48ExactStabilizerDatum`; the datum is not restated here.

## The statement

`HarrisDatumCharacterRealizationExactStabilizerStatement.{uF, uE, uE', uL} : Prop`
says: for every prime `p`, `p`-adic field `F`, finite extension `F'/F`, CM
number fields `E`, `E'`, `L` (with the algebra maps `E → E'`, `E → L`,
`E' → L`), subfield `K₀ ⊆ E`, place data `P Ps : PlaceDatum F F' E E' L`, ring
isomorphisms `φ : E'_{P.v'} ≃ F'` and `φs : E'_{Ps.v'} ≃ F'`, and group
isomorphism `θ : Gal(L/E) ≃ Gal(F̃/F)` (with `F̃` the Galois closure of `F'/F`)
forming a paired-place configuration
(`IsPairedPlaceConfiguration K₀ P Ps φ φs θ`), for every reciprocity family
`e` with `NormalizedReciprocity F e`, and for every continuous character `χ₀`
of `F'^×`, there are characters `χ, χs` of `F'^×` and a Hecke character `ξ`
of `E'` such that

- `Harris.IsProposition48ExactStabilizerDatum e χ χs K₀ P Ps ξ`, and
- `χ u = χ₀ u` for every unit `u` of the valuation ring of `F'` (discrete
  valuation `1`).

In the exact-stabilizer datum, the conjunct on the auxiliary character `χs`
is `GeneralPosition.HasExactWeilStabilizer F F' (weilCharacter F e F' χs)`:
the stabilizer in `W_F`, acting by conjugation, of the restriction of the
Weil character of `χs` to `W_{F̃}` is exactly `W_{F'}`. This is Harris's
condition (4.12), read on the Weil side (the existing definition,
`GeneralPositionStatement.lean`, line 107).

## The single change

The existing declaration is `HarrisDatumCharacterRealizationStatement`
(`Langlands/Global/Arithmetic/HenniartHarrisDatumStatement.lean`, line 90).
The new declaration has the same binders in the same order, the same instance
arguments, the same universe parameters `uF uE uE' uL`, the same hypotheses
(`IsPairedPlaceConfiguration`, `NormalizedReciprocity`) and the same condition
on units, and the single change is in the first conjunct of the conclusion:

```
IsProposition48Datum e χ χs K₀ P Ps ξ
```

becomes

```
Harris.IsProposition48ExactStabilizerDatum e χ χs K₀ P Ps ξ
```

The existing `IsProposition48ExactStabilizerDatum`
(`HarrisProposition48ExactStabilizerData.lean`, line 40) is
`IsProposition48Datum` with its one conjunct
`IsInGeneralPosition F F' (weilCharacter F e F' χs)` replaced by
`HasExactWeilStabilizer F F' (weilCharacter F e F' χs)`, all other conjuncts
in the same order.

An audit outside the Library compared the elaborated values. The constant
`IsProposition48Datum` occurs once in the existing declaration's value; replacing it by
`Harris.IsProposition48ExactStabilizerDatum` gives the new value, with the
same type, universe parameters and reducibility, once Lean's auto-generated
auxiliary proof constants (`_proof_k`) are identified. These constants are
proofs that Lean abstracts out of an elaborated term. The module
`HenniartHarrisDatumStatement` reuses the ones it first generated for `IsPairedPlaceConfiguration` (where
`F` is an implicit binder), while this module generates its own (with `F`
explicit), so they differ in name and binder information. Proofs are
irrelevant, and the audit also checked that the two values (after the
replacement) are definitionally equal at reducible transparency.

## Relation to the existing statement

Every exact-stabilizer datum is a datum: the theorem
`Harris.IsProposition48ExactStabilizerDatum.isProposition48Datum`
(`HarrisProposition48ExactStabilizerData.lean`, line 57) applies the
theorem `Langlands.Global.generalPositionOfExactStabilizer` ((4.12) implies
general position) to the replaced conjunct. So the realization stated here is
stronger than the existing one. The module proves this:

```
theorem harrisDatumCharacterRealizationStatement_of_exactStabilizer
    (h : HarrisDatumCharacterRealizationExactStabilizerStatement.{uF, uE, uE', uL}) :
    HarrisDatumCharacterRealizationStatement.{uF, uE, uE', uL}
```

It applies `h` to the same data and maps the datum with
`isProposition48Datum`. It uses only the standard axioms.

On the consumer side
`Harris.proposition48ExactStabilizerStatement_of_proposition48Statement`
(`HarrisProposition48ExactStabilizerStatement.lean`, line 54) proves that
`Proposition48Statement` implies `Proposition48ExactStabilizerStatement`.
The realization here produces exactly the datum that the restated proposition
takes as hypothesis.

## Why the statement is true

This is a reading of the Library at commit `97bd11ee`; the proof is not
given here.

- The existing proof `harrisDatumCharacterRealization_of_halfWeight`
  (`HarrisDatumCharacterRealizationProof.lean`, line 66) builds `χ`, `χs`,
  `ξ` and proves the conjuncts of the datum one by one. It uses general
  position at one place only: the auxiliary character comes from
  `HarrisDatum.exists_generalPosition_of_unitAgreement` (line 85), and the
  general-position conjunct is `hgp e he χs hagrees` (line 182).
- That theorem (`HarrisDatumAuxiliary.lean`, line 38) takes the auxiliary
  character from `auxiliaryCharacterFirstOrder` and shows that every `χs`
  agreeing with it on norm-one units satisfies `HasExactUnitNormStabilizer`
  (`AuxiliaryCharacterStatement.lean`, line 23): the stabilizer of the
  restriction to units of its norm pullback is exactly the subgroup fixing
  `F'`, which is Henniart's condition 3). It derives
  `HasExactWeilStabilizer F F' (weilCharacter F e F' χs)` from this with
  `unitNormWeilStabilizerTransport`, and only at the last step applies
  `generalPositionOfExactStabilizer` (lines 89–90).
- Stopping before that last step gives the exact-stabilizer conjunct. Every
  other conjunct and the condition on units are proved as before. The
  half-weight input is supplied by `cmHalfWeightCharacter`, as in the
  unconditional `harrisDatumCharacterRealization`
  (`HenniartHarrisDatumProof.lean`, line 11).

## What is not claimed

`HarrisDatumCharacterRealizationExactStabilizerStatement` is not proved here;
it is proved as `harrisDatumCharacterRealizationExactStabilizer` (module
`HenniartHarrisDatumExactStabilizerProof`). Only the implication to the
existing statement is proved here. The
existing `HarrisDatumCharacterRealizationStatement`, its proof and the
common-base `HenniartHarrisDatumStatement` are unchanged. The common-base form
is not restated here.

## Sources

- G. Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur
  un corps p-adique*, Invent. Math. 139 (2000), 439–455, source
  `henniart-2000-simple-proof` (PDF page = printed page − 438).
  - §3.4, condition 3), printed p.449 (PDF p.11): "Le caractère `X_{0'}` est
    `L_{0'}/F_{0'}` régulier, au sens où le stabilisateur dans
    `Gal(L̃_{0'}/F_{0'})` de la restriction à `U_{L̃_{0'}}` de
    `X_{0'} ∘ N_{L̃_{0'}/L_{0'}}` est `Gal(L̃_{0'}/L_{0'})`". The stabilizer
    of the full character `X_{0'} ∘ N` contains `Gal(L̃_{0'}/L_{0'})` and is
    contained in the stabilizer of its restriction to units, so this unit
    condition implies the exact-stabilizer condition (4.12).
  - §3.6, Lemme 3, printed p.451 (PDF p.13): a character `X` satisfying the
    three conditions of 3.4 with prescribed restriction to `U_0`. Its proof
    chooses the component at `0'` satisfying condition 3) of 3.4, "c'est
    possible d'après la preuve du Lemme 4.7 de [Ha 2]".
- M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
  n < p*, Invent. Math. 134 (1998), 177–210, source
  `harris-1998-local-langlands` (PDF page = printed page − 176).
  Proposition 4.8, printed p.201 (PDF p.25). Condition (4.12), in the proof of
  Lemma 4.7, printed pp.204–206 (statement of (4.12) on p.204, PDF p.28): with
  `G = Γ_F`, `H = Γ_{F'}` and `χ̃(*) = χ(*) ∘ N_{F̃/F'}`,
  `H = {g ∈ G | g χ̃(*) = χ̃(*)}`.
- Design: plan note `operator-external-inputs-plan-2026-11-16`,
  Section 4.8, Remark 4.2 (TeX lines 859–894) and the paragraph "The remark
  and the Library's statements" (TeX lines 897–912). The plan note is
  design guidance, not a source of the statement.
