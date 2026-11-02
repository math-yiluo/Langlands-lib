# `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_PolarisationRosati`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_AlgebraicGeometry_PolarisationRosati.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Polarisation conditions for a relative group law (namespace `AlgebraicGeometry.Polarisation`), for
`f : A ⟶ Spec S` with FLT relative group law `L`.

- `idPt f`: the identity of `A` as a point of `A` over `f`; `negMor f L : A ⟶ A`, the inverse of
  `idPt` for `L` (the inversion morphism), with `negMor_over`; `addMor f L : A ×_S A ⟶ A`, the
  product of the two projections for `L` (the addition morphism), with `addMor_over`.
- `LocIsoOnBase g M M'` (for `g : X ⟶ Spec S'`): every point of `Spec S'` has an open
  neighbourhood `U` over whose preimage the modules `M` and `M'` become isomorphic.
- `IsSymmetric f L 𝓛`: `(negMor)^* 𝓛` and `𝓛` are locally isomorphic over the base.
- `mumfordBundle f L 𝓛 = m^* 𝓛 ⊗ (pr₁^* 𝓛^∨ ⊗ pr₂^* 𝓛^∨)` on `A ×_S A` (with `m = addMor`).
- `sliceAt f x : A_T ⟶ A ×_S A` for a point `x` of `A` over `t : T ⟶ Spec S`, the map
  `(pr₁, x ∘ pr₂)`.
- `KernelTrivial f L 𝓛`: every point `x` over an affine `Spec R` at which the Mumford bundle
  restricted along `sliceAt x` is locally trivial over the base is the unit;
  `KernelIsTwoTorsion f L 𝓛`: this local triviality holds exactly when `x · x = 1`.
- `RosatiCompatible f L 𝓛 ι hι star`: for a family `ι` of endomorphisms of `A` over `S` and a
  map `star` of the index set to itself, the pullbacks of the Mumford bundle along
  `(pr₁, ι b ∘ pr₂)` and `(ι (star b) ∘ pr₁, pr₂)` are locally isomorphic over the base, for each
  `b`.

## Declarations

Names, namespaces and statements are the FLT ones.

- def `AlgebraicGeometry.Polarisation.idPt`
- def `AlgebraicGeometry.Polarisation.negMor`
- theorem `AlgebraicGeometry.Polarisation.negMor_over`
- def `AlgebraicGeometry.Polarisation.addMor`
- theorem `AlgebraicGeometry.Polarisation.addMor_over`
- def `AlgebraicGeometry.Polarisation.LocIsoOnBase`
- def `AlgebraicGeometry.Polarisation.IsSymmetric`
- def `AlgebraicGeometry.Polarisation.mumfordBundle`
- def `AlgebraicGeometry.Polarisation.sliceAt`
- def `AlgebraicGeometry.Polarisation.KernelTrivial`
- def `AlgebraicGeometry.Polarisation.KernelIsTwoTorsion`
- def `AlgebraicGeometry.Polarisation.RosatiCompatible`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_SheafOfModules_MonoidalV2` (Library).
Other imports: none.
