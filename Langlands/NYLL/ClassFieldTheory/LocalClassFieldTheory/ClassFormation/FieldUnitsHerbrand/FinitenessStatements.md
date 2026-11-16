# NYLL M143.001: finiteness of degree-zero Tate cohomology of field units

This pair extracts the statement of M143.001 from Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/FieldUnitsHerbrand.lean`.
The pinned file has SHA-256
`e99939deae987f0352abc11da0638814ed6376bb248fe9b958b2a49c53a515f7`
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
| M143.001 | `LocalClassFieldTheory.unitsTateH0FiniteOfIntegerUnitsHerbrand` | `Langlands.NYLL.LocalClassFieldTheory.unitsTateH0FiniteOfIntegerUnitsHerbrandStatement` |

The source context is lines 22–41; the omission command is line 43,
the docstring is lines 44–46, and the theorem statement is lines 47–54.
The proof on lines 54–62 is omitted. M143.002 is outside this pair.

## Complete telescope and proposition

The Lean file spells out the section variables on lines 35–41 as
declaration parameters, applying the source `omit [IsGalois K L] in`
by leaving out that instance. Explicit parameters retain the topology and
local-field hypotheses, which Lean would otherwise drop from an extracted
definition whose conclusion does not use them. Its complete elaborated
telescope is, in the source order and binder kinds,

```lean
(K L : Type) [Field K] [ValuativeRel K]
[Field L] [ValuativeRel L] [TopologicalSpace L]
[IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
[IsIntegralClosure (ValuativeRel.valuation L).integer
  (ValuativeRel.valuation K).integer L]
(g : Gal(L/K))
(hg : ∀ σ : Gal(L / K), σ ∈ Subgroup.zpowers g)
(hU :
  letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  HerbrandQuotientDefined (Gal(L / K))
    (ValuativeRel.valuation L).integerˣ g)
```

Both fields are in the source universe `Type` (`Type 0`). There is no
`IsGalois K L` parameter. The valuation structures on both fields, topology
and nonarchimedean local-field structure on `L`, extension of valuations
and integral-closure hypothesis remain. The generator condition `hg` is an
explicit argument in its source position, even though the extracted
conclusion does not use it. The hypothesis `hU` retains its own local
integer-unit action; it does not introduce a global instance or a separate
action parameter.

The conclusion is the source conclusion verbatim:

```lean
Finite (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0)
```

Here `Rep.ofAlgebraAutOnUnits K L` is Mathlib's actual integer representation
of `Gal(L / K)` on the additive version of `Lˣ`. `tateCohomology` is
Mathlib's actual Tate cohomology construction, evaluated in degree zero.
The integer-unit finiteness premise is the actual
`HerbrandQuotientDefined`: both the fixed-subgroup/norm-image quotient and
the norm-kernel/augmentation-image quotient for the supplied generator are
finite. The target therefore asserts finiteness of actual field-unit Tate
cohomology from the retained source hypotheses.

The original docstring describes the proof as deriving finiteness through
the valuation sequence and transporting it across a comparison equivalence.
This pair records its proposition; it does not implement that proof or
claim the comparison has been proved here.

## Published objects and imports

The target uses the following existing objects:

- `Langlands.NYLL.LocalClassFieldTheory.galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure`,
  in `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.IntegerDefinitions`;
- `Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandQuotientDefined`,
  in `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandFiniteness.Definitions`;
- Mathlib's `Rep.ofAlgebraAutOnUnits`, available through
  `Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90`;
- Mathlib's `tateCohomology`, from
  `Mathlib.RepresentationTheory.Homological.TateCohomology.Basic`.

The additional published import
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.Definitions`
supplies Mathlib's local-field context and the adapted namespace opened
by the source.

The source import of `Mathlib.SetTheory.Cardinal.Finite` is retained. The
four source NYLL imports of `CohomologyBridge`, `Hilbert90`,
`ValuationHerbrand` and `ValueGroupCohomology` are replaced by the five
modules above that supply the objects and context needed by the proposition. Proofs
and comparison maps used only in the omitted proof body are not needed to
state this target. The integer-unit action in `hU` is the published
integral-closure restriction followed by the induced action on units.

## Modifications

Worker 230 made the following changes on 16 November 2026:

1. Prefix the namespace and NYLL namespace opens with `Langlands.NYLL`;
   retain the noncomputable section and scoped valuation notation. Spell
   out the source section variables as declaration parameters, applying
   its `IsGalois` omission and retaining all other hypotheses explicitly.
2. Replace imports as documented above, reusing published objects by Lean
   name.
3. Extract the theorem type as a `def` returning `Prop`, append `Statement`
   to its name and omit the proof. Preserve every explicit argument and
   the `letI` inside `hU`. No proof assumptions or helper constructions are
   introduced.
4. Apply `set_option linter.unusedVariables false in` to this declaration
   alone because some source hypotheses and the premises `hg` and `hU`
   are unused in the extracted conclusion. The option does not change
   the declaration's type or its parameter retention.
5. Replace the module prose by a modification notice and explain the
   source docstring here. Retain the original copyright, author and
   Apache-2.0 header verbatim.

The retained license and notice are `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`. This pair is a statement only. It does not discharge
the theorem's proof, M143.002 or a host class-formation or reciprocity
target.

## Verification

The source telescope, generator premise, local action scope and conclusion
were compared directly with the pinned original. Development check
`dd05e572-996e-48b0-896d-1400a891b7f3` on 16 November 2026 compiled
the module with zero errors or warnings in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`. Exact declaration inspection
reported `statement_returns_prop: true` and no universe parameters. A
private `#check` confirmed the complete telescope printed above, including
the topology and local-field instances and the absence of `IsGalois`.
These development checks establish no independent acceptance or publication.
