# NYLL M142.002: the value-group Herbrand quotient is defined

This pair extracts the statement of M142.002 from Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/ValuationHerbrand.lean`.
The pinned file has SHA-256
`fc840414815c6b092d5cbc41cfb13cde82fee786a59ee24fbe46f66126a6b89d`
and is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
It belongs to registered collection
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Original name | Adapted name |
| --- | --- | --- |
| M142.002 | `LocalClassFieldTheory.galoisGroupValueGroup_herbrandQuotientDefined` | `Langlands.NYLL.LocalClassFieldTheory.galoisGroupValueGroup_herbrandQuotientDefinedStatement` |

The source context is lines 22–39; the omission command is lines 68–72,
the docstring is lines 73–75, and the theorem statement is lines 76–79.
The proof on lines 79–81 is omitted. The other source declarations,
M142.001 and M142.003, are outside this pair.

## Complete telescope and proposition

The Lean file copies the section variable lines 34–39 verbatim. The source
omission command removes `[ValuativeRel K]`, `[ValuativeRel L]`,
`[TopologicalSpace L]`, `[IsNonarchimedeanLocalField L]`,
`[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]`
and the integral-closure instance for the two valuation integer rings.
The elaborated telescope, in order and with its original binder kinds, is

```lean
(K L : Type) [Field K] [Field L] [Algebra K L]
[FiniteDimensional K L] (g : Gal(L/K))
```

Both fields are in the source universe `Type` (`Type 0`); they do not have
an arbitrary new universe parameter. There is no `IsGalois`, cyclicity,
generator or valuation hypothesis. The explicit `g` is any element of
the actual algebra-automorphism group `Gal(L / K)`.

The proposition body is the source statement verbatim:

```lean
letI := galoisGroupValueGroupMulDistribMulAction K L
HerbrandQuotientDefined (Gal(L / K)) (Multiplicative Int) g
```

The local instance is the published M140.005 trivial action on the
multiplicative version of the additive integer group. The actual
`HerbrandQuotientDefined` is the conjunction of finiteness of `HerbrandH0`
and `HerbrandHMinusOne` for that action and the supplied `g`.
Those are the concrete fixed-subgroup/norm-image quotient and
norm-kernel/augmentation-image quotient. Thus the assertion says that both
low-degree value-group quotients are finite. It supplies neither a proof
nor an assumed finiteness instance.

## Published objects and imports

The actual names used by the proposition are

- `Langlands.NYLL.LocalClassFieldTheory.galoisGroupValueGroupMulDistribMulAction`,
  in `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.Definitions`;
- `Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandQuotientDefined`,
  in `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandFiniteness.Definitions`.

The latter imports the actual Herbrand groups from
`Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.HerbrandQuotients.Definitions`.
The additional import of
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.IntegerDefinitions`
supplies the source valued-field context used before the omission command.
Mathlib supplies `Gal`, `FiniteDimensional`, `Multiplicative Int` and `Finite`.
All of these are existing objects imported by Lean name.

## Modifications

Worker 230 made the following changes on 16 November 2026:

1. Prefix the declaration namespace and source NYLL namespace opens with
   `Langlands.NYLL`. Keep the noncomputable section, scoped valuation
   notation, section variable lines and omission command.
2. Replace the source imports of `HerbrandFiniteness` and
   `ValueGroupCohomology` by the three published modules listed above.
   Proofs used only in the source theorem body are not imported.
3. Extract the theorem type as a `def` returning `Prop`, append `Statement`
   to its name and omit its proof. The local `letI` and all objects are
   unchanged. No instances, helpers, assumptions or options are added.
4. Replace the module prose by a modification notice and explain the
   source docstring here. The original copyright, author and Apache-2.0
   header remains verbatim.

The retained license and notice are `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`. This pair is a statement only; proofs and the
remaining source units are separate obligations.

## Verification

The source telescope and proposition were compared directly with the
pinned original. On 16 November 2026 the project Lean service check
`304eb40c-8f5c-4686-ae9a-40a795d09190`, using environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, compiled this module with zero
errors and warnings. Exact inspection reports a definition returning
`Prop` with no universe parameters, as required by the source `Type`
context. This development check establishes neither independent
acceptance nor publication.
