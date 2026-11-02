# `Langlands.AnthropicFLT.Definitions.Def_JacJ1Iface`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_JacJ1Iface.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Interface structures for abelian schemes and Jacobians over an affine base (namespaces
`GoodReductionJacobian` and `MilneJVScheme`).

- `GoodReductionJacobian.AbelianSchemePropertyBundle R f` (a `Prop`-valued structure) for
  `f : A ⟶ Spec R`: `f` is smooth (`smooth`) and proper (`proper`), every topological fibre
  `f⁻¹ {s}` is connected (`connectedFibres`), and `f` carries a relative group law
  (`hasGroupLaw : Nonempty (RelativeGroupLaw R f)`, with FLT's `RelativeGroupLaw` from
  `Def_AlgebraicGeometry_RelativeGroupLaw`).
- `RelativePic0Designation R c`: a scheme `P ⟶ Spec R` with a zero section;
  `trivialPic0Designation` takes `P = Spec R`.
- `AvatarSchemeBridge A D L σ`: an additive group `A` identified with the `σ`-points of
  `D.toBase`, compatibly with addition and zero for the group law `L`;
  `law_one_eq_pts_zero` shows that the unit of `L` is the image of `0`.
- `MilneJVScheme.JacobianSchemeData` bundles such a designation, group law, bridge and abelian
  scheme property bundle over a field; `JacobianSchemeData.ofCore` builds one from a smooth proper
  group scheme with connected fibres and a points identification.

## Declarations

Names, namespaces and statements are the FLT ones.

- structure `GoodReductionJacobian.AbelianSchemePropertyBundle`
- structure `GoodReductionJacobian.RelativePic0Designation`
- def `GoodReductionJacobian.trivialPic0Designation`
- structure `GoodReductionJacobian.AvatarSchemeBridge`
- theorem `GoodReductionJacobian.AvatarSchemeBridge.law_one_eq_pts_zero`
- structure `MilneJVScheme.JacobianSchemeData`
- def `MilneJVScheme.JacobianSchemeData.ofCore`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw` (Library).
Other imports: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
