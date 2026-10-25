# Compatible lower embedding in a field tower

`Langlands.NYLL.PortInternal.M262.d004` takes a supplied embedding of the upper
field into the base field's separable closure and restricts it along the actual
tower algebra map. Its complete telescope and construction are:

```lean
(K E L : Type)
[Field K] [Field E] [Field L]
[Algebra K E] [Algebra E L] [Algebra K L]
[IsScalarTower K E L]
(iL : L →ₐ[K] SeparableClosure K) :
E →ₐ[K] SeparableClosure K :=
iL.comp (IsScalarTower.toAlgHom K E L)
```

All three fields lie in `Type 0`. The result is a `K`-algebra homomorphism whose
underlying function sends `x : E` to `iL (algebraMap E L x)`. Compatibility comes
from composition with the given tower map; no lower embedding is independently
chosen. The field structures, three algebra structures, scalar-tower instance,
and upper embedding are the only inputs. There are no finite-dimensionality,
normality, Galoisness, valuation, topology, or local-field assumptions.

This file contains one data definition. It supplies no field-range inclusion,
Galois restriction theorem, intrinsic reciprocity data, or local reciprocity
result. Those are separate units. In particular the private source abbreviations
M262.001–003 do not occur in this construction.

## Original source and declaration map

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/GeneralTowerNaturality.lean`,
lines 44–51. Its file SHA-256 is
`a81fa466df15d0d72f24428f0780a68b9a9f434fa4d27746beafe71bfae521c0`.
The retained original is in the project literature folder
`External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
It is registered as `external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The full original module was read and its hash verified. No matching NYLL errata
were found in the project or current Library `notes/errata` on 25 October 2026;
the published feasibility inventory records no patch10 change to this module.

| Original declaration | Adapted declaration | Scope |
| --- | --- | --- |
| Private `LocalClassFieldTheory.towerLowerEmbedding` (M262.004) | Public `Langlands.NYLL.PortInternal.M262.d004` | Identical telescope, return type and composition |

The public name follows the reserved internal-support naming scheme in
`notes/reuse/nyll-public-port-plan.md`, section 3, and
`notes/reuse/nyll-public-port/m259-m262.md`, row M262.004. Making this source-private
helper public allows later tower units to share the same lower embedding.

## Imports and modification record

The sole direct import is `Mathlib.FieldTheory.IsSepClosed`, which supplies the
absolute abbreviation `SeparableClosure`. The construction reuses Mathlib's
`AlgHom.comp` and `IsScalarTower.toAlgHom`; their definitions are in
`Mathlib/Algebra/Algebra/Hom.lean`. Thus every transitive import is in the
approved Mathlib environment. No external NYLL repository module is imported.
The entry module compiled and the declaration was inspected in approved environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) with zero errors or warnings.
The complete printed telescope and body retain exactly the inputs above, no
universe parameters, and only the standard axioms `propext`, `Classical.choice`
and `Quot.sound`. These development checks establish the reduced import closure;
independent review and publication are separate requirements.
The inventory's predecessor chain is conservative scheduling information,
not a dependency of this body.

The adaptation moves the declaration into `Langlands.NYLL.PortInternal.M262`,
renames it to the reserved public helper `d004`, extracts it into the single
`GeneralTowerNaturality/U004/Definitions` module, and replaces the source's broad
imports with the Mathlib import above. The source's `noncomputable section` is
retained. The field universes, argument order, hypotheses, return type and body
are unchanged. Worker 100 prepared this unit using Worker 29's source extraction
and reduced-import analysis; this worker attribution is separate from the
original author's copyright.

## License

The Lean file retains the original copyright and author header:
Copyright (c) 2026 Naganori Yamaguchi; Authors: Naganori Yamaguchi
(assisted by OpenAI Codex). It remains under Apache-2.0. The already published
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are reused unchanged through
`repository_paths`; both are byte-identical to the pinned originals. The latter's
file inventory and the ClassFieldTheory `ANTHROPIC_FLT_SOURCE.md` table do not
list this source module. This unit imports no other NYLL module, so no additional
source-specific attribution file applies to its extracted code.
