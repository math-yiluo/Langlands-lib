# `Langlands.AnthropicFLT.Definitions.Def_Mathlib_Algebra_IsDirectLimit`

Ported module of the proof submitted by task `80ab0ad1-6602-4bc6-8c52-3f88f45f4c83` (descent of schemes of finite presentation along finitely generated subalgebras). Definitions module.

## Source and licence

Port of `Definitions/Def_Mathlib_Algebra_IsDirectLimit.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` (section 1) lists this whole file as taken from `FLT/Mathlib/Algebra/IsDirectLimit.lean` of the Imperial College London FLT project (<https://github.com/ImperialCollegeLondon/FLT>), Copyright (c) 2025 Madison Crim; authors: Madison Crim; Apache License, Version 2.0.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The header also reproduces the upstream notice recorded in FLT `ATTRIBUTION.md` (see Source).
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Defines the predicate `IsDirectLimit f g`: for a directed system of types `M i` with transition maps
`f i j h` and maps `g i : M i → P`, the maps `g i` are compatible with the transition maps, every element
of `P` is some `g i mi`, and `g i mi = g j mj` holds only when `mi` and `mj` agree at some later index.
(fields `surj`, `inj`, `compatibility`). It proves the basic consequences (`compatibility'`,
`is_injective`, `is_surjective`, chosen preimages), the induced map `lift` out of a direct limit with
`lift_of`, the equivalence `Equiv` between two direct limits of the same system, and module-theoretic
versions: an instance saying that Mathlib's `Module.DirectLimit` is a direct limit,
`IsDirectLimit.Module.lift` with `lift_of` and `lift_unique`, and `IsDirectLimit.Module.linearEquiv`. The descent proofs use it only to say that a ring `A` is the direct limit of its
finitely generated subalgebras.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- class `IsDirectLimit`
- theorem `IsDirectLimit.compatibility'`
- theorem `IsDirectLimit.is_injective`
- theorem `IsDirectLimit.is_surjective`
- def `IsDirectLimit.preimage_index`
- def `IsDirectLimit.preimage`
- theorem `IsDirectLimit.image_preimage`
- def `IsDirectLimit.lift`
- theorem `IsDirectLimit.lift_of`
- def `IsDirectLimit.Equiv`
- lemma `IsDirectLimit.Equiv_apply`
- lemma `IsDirectLimit.linearEquiv_symm_apply`
- unnamed instance `instance [DecidableEq ι] [Nonempty ι] : IsDirectLimit (f · · ·) (Module.DirectLimit.of R ι M f ·)`
- theorem `IsDirectLimit.Module.compatibility_module`
- def `IsDirectLimit.Module.lift`
- theorem `IsDirectLimit.Module.lift_of`
- theorem `IsDirectLimit.Module.lift_unique`
- def `IsDirectLimit.Module.linearEquiv`
- lemma `IsDirectLimit.Module.linearEquiv_apply`
- lemma `IsDirectLimit.Module.linearEquiv_symm_apply`

## Dependencies

Ported FLT modules imported: none.
All modules also import `Mathlib`.
