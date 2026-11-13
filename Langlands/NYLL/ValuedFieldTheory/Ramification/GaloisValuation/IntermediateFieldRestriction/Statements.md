# Evaluation of the intermediate-field restriction: statement target

`Langlands.NYLL.RamificationTheory.intermediateFieldRestrictNormalHom_apply_valStatement`
is the evaluation formula for the published restriction
`Langlands.NYLL.RamificationTheory.intermediateFieldRestrictNormalHom`. Take
`sigma : Gal(F/K)` and `x : E`, and view both sides as elements of the ambient
field `Omega`. The restriction of `sigma` to `E`, applied to `x`, equals `sigma`
applied to `x` regarded as an element of `F`. In Lean:

```lean
universe u v
variable {K : Type u} {Omega : Type v}
  [Field K] [Field Omega] [Algebra K Omega]

def intermediateFieldRestrictNormalHom_apply_valStatement
    (E F : IntermediateField K Omega) (hEF : E ≤ F) [Normal K E]
    (sigma : F ≃ₐ[K] F) (x : E) : Prop :=
  E.val (intermediateFieldRestrictNormalHom E F hEF sigma x) =
    F.val (sigma (IntermediateField.inclusion hEF x))
```

This is the statement of source unit M259.002. Defining the proposition does
not prove it.

## Parameters and meaning

The declaration has universe parameters `u` for `K` and `v` for `Omega`.
Neither is restricted to `Type 0`. The parameters, in order, are:

| Binder | Kind | Meaning |
| --- | --- | --- |
| `K` | implicit, `Type u` | Base field |
| `Omega` | implicit, `Type v` | Ambient field |
| `[Field K]`, `[Field Omega]`, `[Algebra K Omega]` | instance-implicit | Field structures and the algebra `Omega / K` |
| `E`, `F` | explicit, `IntermediateField K Omega` | Lower and upper intermediate fields |
| `hEF : E ≤ F` | explicit | Inclusion of `E` in `F` |
| `[Normal K E]` | instance-implicit | Normality of `E / K` |
| `sigma : F ≃ₐ[K] F` | explicit | A `K`-automorphism of `F` |
| `x : E` | explicit | An element of `E` |

The terms in the equation are:

- `intermediateFieldRestrictNormalHom E F hEF sigma : E ≃ₐ[K] E` is the
  published M259.001 restriction. It is Mathlib's `AlgEquiv.restrictNormalHom E`,
  computed with `Algebra E F` given by the inclusion `E → F`.
- `E.val : E →ₐ[K] Omega` and `F.val : F →ₐ[K] Omega` are the subtype inclusions
  of the intermediate fields into `Omega`.
- `IntermediateField.inclusion hEF : E →ₐ[K] F` is the inclusion induced by
  `hEF`.

So the equation lives in `Omega`, and the statement does not depend on the
auxiliary `Algebra E F` instance used inside the definition. Only `E` needs to
be normal. The statement assumes no finite-dimensionality, Galois condition on
`F`, valuation, topology or local-field structure.

## Original source and declaration map

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/Ramification/GaloisValuation/IntermediateFieldRestriction.lean`.
The relevant lines are:

- the docstring at lines 38–39;
- the theorem's telescope and statement at lines 40–44;
- the proof at lines 44–49;
- the section variables at lines 25–26 and `universe u v` at line 23.

The file's SHA-256 is
`bb852d96b0beadbf321ddc6b09359f382e01489c518e50890e25cb9cbb9f57c5`. The source
statement reads:

```lean
theorem intermediateFieldRestrictNormalHom_apply_val
    (E F : IntermediateField K Omega) (hEF : E ≤ F) [Normal K E]
    (sigma : F ≃ₐ[K] F) (x : E) :
    E.val (intermediateFieldRestrictNormalHom E F hEF sigma x) =
      F.val (sigma (IntermediateField.inclusion hEF x)) := by
```

The statement mentions `K` and `Omega`, through `IntermediateField K Omega`, so
all five section binders are parameters of the source theorem, in the order
shown above.

The retained original is in the project literature folder
`External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
It is registered as `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Original declaration | Adapted declaration |
| --- | --- |
| `RamificationTheory.intermediateFieldRestrictNormalHom_apply_val` (M259.002) | `Langlands.NYLL.RamificationTheory.intermediateFieldRestrictNormalHom_apply_valStatement` |
| `RamificationTheory.intermediateFieldRestrictNormalHom` (M259.001) | Published `Langlands.NYLL.RamificationTheory.intermediateFieldRestrictNormalHom` (imported, not redefined) |

Only the first row introduces a declaration in this module. Row M259.002 of the
published partition
[`notes/reuse/nyll-public-port/m259-m262.md`](../../../../../../notes/reuse/nyll-public-port/m259-m262.md)
reserves `Langlands.NYLL.RamificationTheory.intermediateFieldRestrictNormalHom_apply_val`
for the later proof. The `Statement` suffix follows section 3 of
[`notes/reuse/nyll-public-port-plan.md`](../../../../../../notes/reuse/nyll-public-port-plan.md).
No NYLL erratum for this module was found in the current Library's `notes/`.

## Imports and modification record

The only direct import is the published sibling module
`Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.IntermediateFieldRestriction.Definitions`.
It supplies the restriction and, through `Mathlib.FieldTheory.Galois.Basic`,
every Mathlib name used. No external NYLL module is imported.

The adaptation makes three changes:

- it moves the theorem's telescope and conclusion into the Prop-valued
  definition above, keeping the universes, section variables, binder order,
  binder kinds, binder names and conclusion unchanged;
- it omits the source proof;
- it prefixes the namespace with `Langlands.NYLL` and keeps the source's
  `noncomputable section`.

The source docstring is retained. The Lean header records these changes with
Worker 30's dated modification note.

The module compiled with zero errors and zero warnings in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Inspection reports a definition
whose type ends in `Prop` (`statement_returns_prop: true`), with level
parameters `u, v` and only the standard axioms `propext`, `Classical.choice`
and `Quot.sound`. This development check is not independent acceptance.

## Boundary and license

This file defines the proposition only. The theorem
`Langlands.NYLL.RamificationTheory.intermediateFieldRestrictNormalHom_apply_val`
and its proof need a separate proof task once this target is in the Library.
The source proof installs the same two local instances and applies
`AlgEquiv.restrictNormal_commutes sigma E x` under `F.val`.

The Lean file keeps the original copyright and author header unchanged:
Copyright (c) 2026 Naganori Yamaguchi; Authors: Naganori Yamaguchi (assisted
by OpenAI Codex). It remains under Apache-2.0. The already-published
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are reused unchanged and
included through `repository_paths`. Their SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. Worker 30
adapted this unit directly from the pinned original; no other project worker
supplied code. The imported definition module and its Markdown are unchanged.
