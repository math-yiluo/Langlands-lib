# NYLL M073.004: fixed representation and relative coset action agree

Worker 190, 13 November 2026.

## Statement and scope

This pair proves the published proposition
`Langlands.NYLL.ClassFormation.extensionFixedRepresentation_action_coeStatement`
under the required theorem name
`Langlands.NYLL.ClassFormation.extensionFixedRepresentation_action_coe`.
The sole direct import is
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FieldRepresentation.Action.Statements`.
The published statement and its imported definitions remain unchanged.

For an integral representation `A` of `G`, closed subgroups `L ≤ K` and
an explicit proof `hnormal` that `L` is normal inside `K`, the theorem states
that the actual quotient action on the `L`-fixed carrier, coerced to `A.V`,
equals the relative coset action on the same vector:

```lean
((extensionFixedRepresentation A K L hLK hnormal).ρ q a).1 =
  relativeCosetAction A K L hLK
    (extensionFixedRepresentationEquiv A K L hLK hnormal a) q
```

The theorem preserves the complete source telescope: implicit
`G : IntegralRepGroupType` (universe zero), group and topology instances,
explicit `A`, `K L`, containment proof `hLK`, explicit normality proof
`hnormal`, quotient element `q` and fixed vector `a`, in that order.
It adds no finiteness or continuity premise.

## Implemented proof

```lean
  let := hnormal
  refine Quotient.inductionOn' q ?_
  intro k
  rfl
```

The normality proof is installed locally as an instance, as in the source.
Quotient induction reduces to a representative `k : K.toSubgroup`.
The quotient representation is Mathlib's actual quotient action on the
invariants of the restriction of `A` to `K`. On a representative its
underlying value is `A.ρ k.1 a.1`. The relative coset action is a quotient
lift with the same representative formula.
The carrier equivalence preserves the underlying vector by construction.
Both sides therefore reduce to the same expression, and `rfl` proves
their equality.

The published definitions used through the statement are:

- `CyclicCohomology.extensionFixedRepresentation`, from
  `GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`,
  built with `Rep.quotientToInvariants` and `Rep.res`.
- `ClassFormation.extensionFixedRepresentationEquiv`, from
  `Reciprocity.FieldRepresentation.FixedCarrier.Definitions`, whose
  forward map changes only the proof that the vector is fixed.
- `ClassFormation.relativeCosetAction`, from
  `Degree.Norm.Definitions`, defined by `Quotient.liftOn'` and the formula
  `fun k => A.ρ k.1 a.1`.

The proof uses Mathlib's `Quotient.inductionOn'` and computation of these
definitions. It invokes no other NYLL proof theorem. In particular, it
does not import or reproduce the separate theorem `relativeCosetAction_mk`.

## Original source and modifications

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FieldRepresentation.lean`,
lines 87–100. The section variable at line 31 fixes the universe of `G`.
The theorem signature occupies lines 87–95 and its proof lines 96–100.
The same source defines the carrier equivalence at lines 35–57.
Its file SHA-256 is
`8124bbdd42702e1dba3060f8a2f14c6d66ead33c113d0b4310bc6157fea19bb9`.

The original `relativeCosetAction` is at
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Norm.lean:39–56`.
Its representative formula, `relativeCosetAction_mk`, is proved by `rfl`
at lines 60–65. The source proof of M073.004 rewrites by that formula
before using `rfl`; the adapted proof performs the same definitional
reduction directly after quotient induction. It requires no prerequisite
publication for that reflexive helper.

The extension subgroup is defined at
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean:51–54` by
`L.toSubgroup.subgroupOf K.toSubgroup`. The source quotient representation
is at lines 61–68 of that file. These are the constructions used by the
Library definitions above.

The retained original snapshot is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Registered sources are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

| Source declaration | Published proof declaration |
| --- | --- |
| `ClassFormation.extensionFixedRepresentation_action_coe` | `Langlands.NYLL.ClassFormation.extensionFixedRepresentation_action_coe` |

Other modifications are the namespace prefix `Langlands.NYLL`, the
focused published-statement import, expressing the result as the existing
target proposition applied to all its parameters, and expanding
`extensionSubgroup` to its exact Mathlib body in the telescope.
The unused source `BigOperators` scope is omitted.
No additional public helper or global instance is introduced.

The original copyright, Apache-2.0 license statement and author header are
preserved in the Lean file. The inherited `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` remain unchanged, with respective SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

This support lemma proves M073.004 only. It proves no norm identity or
host class-formation, cup-product, transfer, Tate-cohomology or
local-reciprocity target.

## Development validation

Lean service check `c63ba52d-34e8-4536-940f-f22cae8ac064` compiled the final
proof in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`, without errors
or warnings. An earlier declaration inspection in check
`5c5fd11e-7e6c-43c5-8a27-4628dee42407` confirmed the source's universe-zero
telescope and only `propext`, `Classical.choice` and `Quot.sound` as assumptions;
the subsequent edit restored the source's `let := hnormal` spelling to remove
a style warning. The theorem result is the published target applied to all
its parameters. Independent review, exact-target validation and publication
remain separate.
