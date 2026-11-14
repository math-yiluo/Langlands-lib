# Relative norms of intermediate-field units: comparison targets

The paired Lean file extracts two propositions from Naganori Yamaguchi's
ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableUnitsNorm.lean`
(SHA-256 `b725f9b453be02ebc61de24d8c9a3f32b87f438471b2423357c1edf54a76fcaa`).
The readable original is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
It is registered as `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The inventory `notes/reuse/nyll-public-port/m073-m096.md`, section M096,
records no patch10 modification of this source file. No applicable NYLL
erratum was found in the Library's `notes/errata/`.

## Exact source correspondence

| Unit and source lines | Original theorem | Adapted proposition definition |
| --- | --- | --- |
| M096.005; docstring 119–120, theorem type 121–128, proof 128–171 | `LocalClassFieldTheory.relativeNorm_intermediateFieldUnit_val` | `Langlands.NYLL.LocalClassFieldTheory.relativeNorm_intermediateFieldUnit_valStatement` |
| M096.006; docstring 173–174, theorem type 175–182, proof 182–186 | `LocalClassFieldTheory.relativeNorm_intermediateFieldUnit` | `Langlands.NYLL.LocalClassFieldTheory.relativeNorm_intermediateFieldUnitStatement` |

Both declarations preserve the complete source parameter telescope from
lines 36–37 and 62, in order:

```lean
(K : Type) (Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
(E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]
(x : Eˣ)
```

The fields and intermediate field are explicit. Both field types have universe
zero, with no universe parameters. Both Galois hypotheses and the
finite-dimensional hypothesis are retained. Unlike source M096.004, these
two declarations have no `omit` command. The ambient extension may be
infinite; there is no perfectness, valuation or local-field hypothesis.

## Propositions and meaning

M096.005 asserts the source equality of values in the ambient field:

```lean
((Additive.toMul
  ((relativeNorm (galoisAmbientUnitsRep K Ω)
    (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
    (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
    (intermediateFieldUnitsEquivGaloisFixed K Ω E
      (Additive.ofMul x))).1 : Additive Ωˣ) : Ωˣ) : Ω) =
  algebraMap K Ω (Algebra.norm K (x : E))
```

The abstract relative norm runs from the coefficients fixed by the fixing
subgroup of `E` to those fixed by the fixing subgroup of the bottom
intermediate field. The inclusion of an `E`-unit into the first fixed
subgroup is the actual `intermediateFieldUnitsEquivGaloisFixed`. Forgetting
the output's fixedness and additive notation, and then taking its unit value,
is asserted to give the ordinary algebra norm included into `Ω`.

M096.006 asserts the source equality in the base fixed-unit subgroup:

```lean
relativeNorm (galoisAmbientUnitsRep K Ω)
    (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
    (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
    (intermediateFieldUnitsEquivGaloisFixed K Ω E
      (Additive.ofMul x)) =
  baseUnitsEquivGaloisAmbientFixed K Ω
    (Additive.ofMul (normUnits K E x))
```

Here `normUnits` is the published restriction of `Algebra.norm K` to units.
The right side uses the actual base-field unit equivalence, so the equality
compares elements of the same fixed coefficient subgroup. Each body is the
original proposition literally, with its names resolved in `Langlands.NYLL`.
The source proofs are omitted; the paired Lean file defines the two
propositions and does not prove them.

## Reuse, finiteness and modifications

The focused imports are:

- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.BaseUnits.Definitions`,
  supplying M096.001 and transitively the M088.006 intermediate-field
  equivalence and its published prerequisites;
- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.Finite.Definitions`,
  supplying the published instance
  `Langlands.NYLL.LocalClassFieldTheory.baseFixingExtensionQuotient_finite`
  (M096.003) and the fixing-subgroup inclusion;
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions`,
  supplying published M024.009 `Langlands.NYLL.ClassFormation.relativeNorm`;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions`,
  supplying published M092.002 `Langlands.NYLL.LocalFieldTheory.normUnits`
  and the original Mathlib norm import.

The published relative norm takes finiteness of the quotient of the base
fixing subgroup by
`(closedFixingSubgroup K Ω E).toSubgroup.subgroupOf
  (closedFixingSubgroup K Ω ⊥).toSubgroup`.
The source instance M096.003 uses `extensionSubgroup`, whose published
abbreviation is exactly this `subgroupOf`. Typeclass inference therefore
uses that existing instance with the source hypotheses; no instance,
alternate norm or local copy of a sibling definition is introduced.
Both `relativeNorm` and `normUnits` are reused by their published Lean names.
The norm and additive fixed-subgroup interfaces are not replaced by assumed
maps or arbitrary coefficient groups.

Worker 324 extracted just M096.005 and .006 into this focused module on
14 November 2026, prefixed `LocalClassFieldTheory` with `Langlands.NYLL`,
changed each `theorem` to a `def` returning `Prop`, appended `Statement`,
and omitted the source proof. The two docstrings are replaced by
proposition-specific descriptions. The broad source imports and whole-file
introduction are replaced by the focused imports and modification notice.
The source namespace openings are consolidated, and the unused
`BigOperators` scope is omitted. The noncomputable section,
`FiniteGaloisIntermediate` section, source parameter declarations and their
order remain. No equality, coercion, binder kind or hypothesis is changed.
Existing Mathlib and Library declarations are imported by Lean name;
no exact existing target with these NYLL equivalences was found.

## Development checks

Focused `lean_check` inspections in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) succeeded with zero errors and
warnings. Inspection `352c025a-ae5c-4b20-9139-25e930684763` checks M096.005,
and `15b4f5ca-42fd-469d-a6d2-7e39957d6dd1` checks M096.006. Both explicitly
report `statement_returns_prop: true`, an empty universe-parameter list,
and only `propext`, `Classical.choice` and `Quot.sound` as axioms.
These are development checks; independent acceptance and publication are
separate requirements.

## Attribution and scope

The original copyright, author and Apache-2.0 header is retained verbatim
in the Lean file. The published `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` retain the original license and notices. Worker 324's
extraction and modifications are recorded above and in the Lean header.
These are support statement targets only; this contribution discharges no
host class-formation, cup, transfer, Tate or reciprocity target.
