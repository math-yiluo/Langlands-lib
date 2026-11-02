# `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_AlgebraicGeometry_OModulePresheafEulerChar.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Čech dimensions and Euler characteristic of FLT's `OModulePresheaf π` (presheaves of modules
over `V`, for `π : V ⟶ Spec R`) with respect to an ordered finite affine cover `K` (namespace
`AlgebraicGeometry.OModulePresheaf`).

- `cechFinrank F K i`: the `R`-rank (`Module.finrank R`) of the `i`-th Čech cohomology group of `F`
  for `K`: `F.H0 K` for `i = 0` and `F.HSucc K i` for `i + 1`; `cechFinrank_zero` and
  `cechFinrank_succ` restate the two cases.
- `eulerChar F K`: the alternating sum `∑_{i < |K.ι|} (-1)^i · cechFinrank F K i` in `ℤ`, over the
  first `Fintype.card K.ι` degrees; `eulerChar_def` restates it.

## Declarations

Names, namespaces and statements are the FLT ones.

- def `AlgebraicGeometry.OModulePresheaf.cechFinrank`
- theorem `AlgebraicGeometry.OModulePresheaf.cechFinrank_zero`
- theorem `AlgebraicGeometry.OModulePresheaf.cechFinrank_succ`
- def `AlgebraicGeometry.OModulePresheaf.eulerChar`
- theorem `AlgebraicGeometry.OModulePresheaf.eulerChar_def`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech` (Library).
Other imports: `Mathlib.LinearAlgebra.Dimension.Finrank`, `Mathlib.Algebra.BigOperators.Group.Finset.Basic`.
