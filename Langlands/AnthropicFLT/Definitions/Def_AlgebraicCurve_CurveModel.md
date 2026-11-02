# `Langlands.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_AlgebraicCurve_CurveModel.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Smooth proper models of function fields of curves (namespace `AlgebraicCurve`).

- `baseToFunctionField c`: for an integral scheme `C` over `Spec K`, the ring map `K → K(C)` to the
  function field (global sections of `Spec K`, then of `C`, then the germ at the generic point).
- `CurveModel K L` (a structure, for a field extension `L / K`): an integral scheme `C` with a
  proper, smooth of relative dimension `1` morphism `toBase : C ⟶ Spec K`, a ring isomorphism
  `ffEquiv : L ≃+* K(C)` compatible with the maps from `K`, a bijection `placeOfPoint` from the
  closed points of `C` to the places of `L / K` (FLT's `Place K L`) such that the image of the stalk at
  each closed point is the valuation ring of its place (`range_stalk_eq`), and such that every
  finite set of points lies in an affine open. Its three instance fields are made instances.
- `CurveModel.functionFieldAlgebra`, `ffAlgEquiv` (the `K`-algebra isomorphism `L ≃ₐ[K] K(C)`),
  `placeEquiv` (closed points ≃ places) and, for algebraically closed `K`, `pointEquivPlace`
  (sections `Spec K ⟶ C` of `toBase` ≃ places, through FLT's `pointEquivClosedPoint`), with their
  `_apply` lemmas.

## Declarations

Names, namespaces and statements are the FLT ones.

- def `AlgebraicCurve.baseToFunctionField`
- structure `AlgebraicCurve.CurveModel`
- abbrev `AlgebraicCurve.CurveModel.functionFieldAlgebra`
- def `AlgebraicCurve.CurveModel.ffAlgEquiv`
- theorem `AlgebraicCurve.CurveModel.ffAlgEquiv_apply`
- def `AlgebraicCurve.CurveModel.placeEquiv`
- theorem `AlgebraicCurve.CurveModel.placeEquiv_apply`
- def `AlgebraicCurve.CurveModel.pointEquivPlace`
- theorem `AlgebraicCurve.CurveModel.pointEquivPlace_apply`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup` (same contribution).
Other imports: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.AlgebraicGeometry.FunctionField`, `Mathlib.AlgebraicGeometry.AlgClosed.Basic`, `Mathlib.FieldTheory.RatFunc.Basic`.
