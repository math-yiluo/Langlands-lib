# `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_AlgebraicGeometry_PolarisedAbelianScheme.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 18 here); in 7 lines the replacements `Type` (universe 0) → `Type uz` (6 places), `Scheme.{0}` → `Scheme.{uz}` (1 place) are made, and these lines are otherwise unchanged. Consequently the definitions and statements become universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

Polarised abelian schemes with level structure and their fine moduli (namespaces
`GoodReductionJacobian.RelativeGroupLaw` and `AlgebraicGeometry`).

- `RelativeGroupLaw.finComb L t x c`: for points `x₀, …, x_{m-1}` of `A` over `t` and exponents
  `c`, the product `∏ᵢ xᵢ^{cᵢ}` in the group of points for the group law `L`.
- `Scheme.Modules.geomFibreH0Finrank f M k sk`: for `f : A ⟶ Spec S`, a module `M` on `A` and a ring
  map `sk : S → k` to a field, the `k`-dimension (`Module.finrank`) of the global sections of the
  pullback of `M` to the fibre `A ×_{Spec S} Spec k`.
- `PolarisedAbelianScheme g d n S` (a structure in `Type (u + 1)`): a scheme `A` with
  `f : A ⟶ Spec S`, a commutative relative group law `L`, the abelian scheme property bundle,
  fibres of topological Krull dimension `g`, points `P₀, …, P_{2g-1}` over `Spec S` killed by `n`
  that form a basis of the `n`-torsion on every geometric fibre over an algebraically closed field
  (`P_indep`: the combinations with exponents in `Fin n` are distinct; `P_span`: every `n`-torsion
  point is such a combination), and an invertible module `pol` with `ClosedImmersionBySections pol f`
  whose global sections on every geometric fibre have dimension `d`.
- `PolarisedAbelianScheme.Iso u u'`: an isomorphism of the schemes over `Spec S` compatible with the
  group laws and the points `Pᵢ`, under which the pullback of `pol` is locally on the base
  isomorphic to `pol`.
- `PolarisedAbelianScheme.IsPullback φ u u'`: for a ring map `φ : S → S'`, `u'` is a base change of
  `u` along `Spec φ` (a pullback square of schemes compatible with the group laws and the points,
  and the pullback of `pol` isomorphic to `pol'`).
- `PolarisedAbelianScheme.IsFineModuli g d n M πM pt` (a structure of propositions): for
  `πM : M ⟶ Spec B` and an assignment `pt` of a point of `M` over `s : Spec S ⟶ Spec B` to each
  polarised abelian scheme over `S`, `pt` is constant on isomorphism classes, compatible with
  pullbacks, surjective and injective up to `Iso`. Here `B`, `S`, `S'` and `M` are in a universe
  `uz` (FLT: universe `0`); see the changes above.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above.

- def `GoodReductionJacobian.RelativeGroupLaw.finComb`
- def `AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank`
- structure `AlgebraicGeometry.PolarisedAbelianScheme`
- def `AlgebraicGeometry.PolarisedAbelianScheme.Iso`
- def `AlgebraicGeometry.PolarisedAbelianScheme.IsPullback`
- structure `AlgebraicGeometry.PolarisedAbelianScheme.IsFineModuli`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_JacJ1Iface` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation` (same contribution).
Other imports: `Mathlib.Topology.KrullDimension`.
