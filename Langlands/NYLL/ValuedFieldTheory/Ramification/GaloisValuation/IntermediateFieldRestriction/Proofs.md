# Evaluation of the intermediate-field restriction: proof

`Langlands.NYLL.RamificationTheory.intermediateFieldRestrictNormalHom_apply_val`
proves the published target
`Langlands.NYLL.RamificationTheory.intermediateFieldRestrictNormalHom_apply_valStatement`
for every choice of its parameters:

```lean
theorem intermediateFieldRestrictNormalHom_apply_val
    (E F : IntermediateField K Omega) (hEF : E ≤ F) [Normal K E]
    (sigma : F ≃ₐ[K] F) (x : E) :
    intermediateFieldRestrictNormalHom_apply_valStatement E F hEF sigma x
```

with the section variables `{K : Type u} {Omega : Type v} [Field K] [Field Omega]
[Algebra K Omega]` of the statement module. So for intermediate fields `E ≤ F` of
`Omega / K` with `E` normal over `K`, `sigma : Gal(F/K)` and `x : E`,
`E.val (intermediateFieldRestrictNormalHom E F hEF sigma x) =
F.val (sigma (IntermediateField.inclusion hEF x))`.

## Proof

The proof is the source proof, unchanged.

1. It installs the same two local instances that the definition
   `intermediateFieldRestrictNormalHom` (M259.001) uses: the `E`-algebra structure
   on `F` given by `(IntermediateField.inclusion hEF).toRingHom`, and
   `IsScalarTower K E F` from `IsScalarTower.of_algebraMap_eq' rfl`.
2. Under these instances, Mathlib's `AlgEquiv.restrictNormal_commutes sigma E x`
   says that `algebraMap E F` applied to `(sigma.restrictNormal E) x` equals
   `sigma (algebraMap E F x)`.
3. Applying `F.val` to both sides (`congrArg F.val`) closes the goal. The goal
   matches up to definitional unfolding: the target definition unfolds to the
   equation, `intermediateFieldRestrictNormalHom E F hEF sigma` unfolds to
   `sigma.restrictNormal E` for the same instances, `algebraMap E F` is the
   inclusion, and `F.val` after the inclusion of `E` in `F` is `E.val`.

## Imports and scope

The only direct import is
`Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.IntermediateFieldRestriction.Statements`.
It imports the published sibling `Definitions` module, whose only direct import is
`Mathlib.FieldTheory.Galois.Basic`. That Mathlib import supplies
`AlgEquiv.restrictNormal_commutes` and the field, algebra, scalar-tower and
intermediate-field interfaces. No external NYLL module or new helper is imported.
The target and the modules it imports are unchanged.

The theorem retains universe parameters `u, v`, the five section binders in their
source order, and the explicit binders `E`, `F`, `hEF`, then instance binder
`[Normal K E]`, followed by `sigma`, `x`. It requires no finite-dimensionality,
normality of `F`, valuation, topology or local-field hypothesis.

## Source and modifications

Source: Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/Ramification/GaloisValuation/IntermediateFieldRestriction.lean`
(SHA-256 `bb852d96b0beadbf321ddc6b09359f382e01489c518e50890e25cb9cbb9f57c5`),
theorem `RamificationTheory.intermediateFieldRestrictNormalHom_apply_val` at lines
38–49 (inventory M259.002). The retained original is in the project literature folder
`External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`,
registered as `external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`); the attribution
supplement is `nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

| Original declaration | Adapted declaration |
| --- | --- |
| `RamificationTheory.intermediateFieldRestrictNormalHom_apply_val` (M259.002) | `Langlands.NYLL.RamificationTheory.intermediateFieldRestrictNormalHom_apply_val` |

Modifications: the namespace gains the `Langlands.NYLL` prefix; the conclusion is
written as the published target applied to the telescope instead of the
equation it unfolds to; the only import is the statement module. The universes,
section variables, telescope, docstring and tactic proof are unchanged. The theorem
is isolated in this proof module, and its module documentation cites the source
passage. Worker 307 prepared the shared draft for submission on 13 November 2026
and expanded the documentation without changing the proof.

The module compiled with zero errors and zero warnings in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), checked by Worker 307 with
`lean_check` diagnostic `4ddfa289-d3d2-4521-8840-45ed0559fa4e`. Inspection identifies
a theorem with universe parameters `u, v` and only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`. This development check is not independent
acceptance or the staged exact-target validation.

## License

The Lean file keeps the original copyright and author header unchanged:
Copyright (c) 2026 Naganori Yamaguchi; Authors: Naganori Yamaguchi (assisted by
OpenAI Codex). It remains under Apache-2.0. The already-published `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE` are reused unchanged and included through
`repository_paths`. Worker 89 adapted this proof directly from the pinned original;
Worker 307 checked and submitted the shared draft and expanded this documentation.
The unchanged license and notice have SHA-256 hashes
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
