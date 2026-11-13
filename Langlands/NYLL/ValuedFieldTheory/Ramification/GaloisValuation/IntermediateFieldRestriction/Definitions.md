# Restriction between normal intermediate fields

`Langlands.NYLL.RamificationTheory.intermediateFieldRestrictNormalHom` is the
group homomorphism `Gal(F/K) → Gal(E/K)` that restricts a `K`-automorphism of
`F` to `E`. Here `E ≤ F` are two intermediate fields of one ambient extension
`Omega / K`, and `E` is normal over `K`. Its full telescope and body are:

```lean
universe u v
variable {K : Type u} {Omega : Type v}
  [Field K] [Field Omega] [Algebra K Omega]

noncomputable def intermediateFieldRestrictNormalHom
    (E F : IntermediateField K Omega) (hEF : E ≤ F) [Normal K E] :
    (F ≃ₐ[K] F) →* (E ≃ₐ[K] E) := by
  letI : Algebra E F :=
    RingHom.toAlgebra (IntermediateField.inclusion hEF).toRingHom
  letI : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' rfl
  exact AlgEquiv.restrictNormalHom E
```

The declaration has two universe parameters, `u` for `K` and `v` for `Omega`.
Neither is restricted to `Type 0`. The implicit section variables `K` and
`Omega`, their field structures and the algebra `Omega / K` come first. The
explicit `E`, `F` and `hEF` and the instance `[Normal K E]` follow.

## Mathematical content

The body installs two local instances and then uses Mathlib's restriction to a
normal subfield.

- `Algebra E F` is the ring homomorphism underlying the inclusion
  `IntermediateField.inclusion hEF : E →ₐ[K] F`. As an element of `Omega`,
  `x : E` stays the same element inside `F`.
- `IsScalarTower K E F` comes from `IsScalarTower.of_algebraMap_eq' rfl`.
  Both algebra maps `K → F` are the subtype algebra maps of `Omega`, so they
  agree definitionally.
- `AlgEquiv.restrictNormalHom E : Gal(F/K) →* Gal(E/K)` is defined in the
  approved Mathlib file `Mathlib/FieldTheory/Normal/Defs.lean`, lines 194–196.
  It is `MonoidHom.mk'` applied to `fun χ => χ.restrictNormal E`. Its
  multiplicativity is `AlgEquiv.restrictNormal_trans`.

So for `sigma : Gal(F/K)`, the image is the unique `K`-automorphism of `E` that
commutes with `sigma` through the inclusion `E → F`. Mathlib proves this
compatibility as `AlgEquiv.restrictNormal_commutes` (line 176). It needs `E` to
be normal over `K`, and only `E`. The definition assumes nothing about `F` or
`Omega` beyond the field and algebra structures: no finite-dimensionality, no
Galois condition on `F` and no valuation, topology or local-field structure.

This file contains this one definition and nothing else. The evaluation formula
`intermediateFieldRestrictNormalHom_apply_val` is source unit M259.002. It has
its own statement and proof units.

## Original source and declaration map

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/Ramification/GaloisValuation/IntermediateFieldRestriction.lean`.
The relevant source lines are:

- the docstring at lines 28–29;
- the definition at lines 30–36;
- the section variables at lines 25–26;
- `universe u v` at line 23.

The file's SHA-256 is
`bb852d96b0beadbf321ddc6b09359f382e01489c518e50890e25cb9cbb9f57c5`. The
complete 51-line file was read. Its only import is
`Mathlib.FieldTheory.Galois.Basic`.

The retained original is in the project literature folder
`External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
It is registered as `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Original declaration | Adapted declaration | Scope |
| --- | --- | --- |
| `RamificationTheory.intermediateFieldRestrictNormalHom` (M259.001) | `Langlands.NYLL.RamificationTheory.intermediateFieldRestrictNormalHom` | Same universes, telescope, return type and tactic body |

The target name is the one given for row M259.001 in the published partition
[`notes/reuse/nyll-public-port/m259-m262.md`](../../../../../../notes/reuse/nyll-public-port/m259-m262.md).
It follows the naming rule in
[`notes/reuse/nyll-public-port-plan.md`](../../../../../../notes/reuse/nyll-public-port-plan.md).
No NYLL erratum for this module was found in the current Library's `notes/`.

## Imports and modification record

The only direct import is `Mathlib.FieldTheory.Galois.Basic`, which is also the
source's only import. It brings in `IntermediateField`, `IntermediateField.inclusion`,
`Normal` and `AlgEquiv.restrictNormalHom`. Every transitive import lies in the
approved Mathlib environment, and no external NYLL module is imported.

The adaptation makes four changes:

- it prefixes the namespace with `Langlands.NYLL`;
- it splits this definition out as its own `Definitions` module;
- it keeps the module docstring's title but replaces its prose with a citation
  of the source passage (lines 21–36);
- it omits the following theorem (M259.002).

The source's `noncomputable section`, `universe u v` line, section variables,
docstring, argument order, binder kinds, return type and tactic body are
unchanged. The Lean header records these changes with Worker 30's dated
modification note.

The module compiled with zero errors and zero warnings in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Inspection reports a definition
with level parameters `u, v`, using only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`. The source itself targeted Lean
4.35.0-rc2. This development check is not independent acceptance.

## License

The Lean file keeps the original copyright and author header unchanged:
Copyright (c) 2026 Naganori Yamaguchi; Authors: Naganori Yamaguchi (assisted
by OpenAI Codex). It remains under Apache-2.0. The already-published
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are reused unchanged and
included through `repository_paths`. Their SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. Worker 30
adapted this unit directly from the pinned original; no other project worker
supplied code.
