# Group laws on the points of a scheme over a ring

Module `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw`, in namespaces
`NeronModelInfra` and `GoodReductionJacobian`. Schemes and rings live in a fixed universe `u`.
`SchemeHomOver g f` is the type of morphisms over a base from
`Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier`.

## Definitions and results

**Morphisms over a base as morphisms in the over category.** `schemeHomOverToOverHom` and
`overHomToSchemeHomOver` convert between `SchemeHomOver g f` and morphisms `Over.mk g ⟶ Over.mk f`. They
are mutually inverse (`overHomToSchemeHomOver_schemeHomOverToOverHom`,
`schemeHomOverToOverHom_overHomToSchemeHomOver`) and give the equivalence `schemeHomOverEquivOverHom`
(lemmas `schemeHomOverToOverHom_left`, `overHomToSchemeHomOver_coe`, `schemeHomOverEquivOverHom_apply`,
`schemeHomOverEquivOverHom_symm_apply`).

**Relative group laws.** Fix `f : A ⟶ Spec R`.

- `schemeHomOverComp ψ hψ x`, for `ψ : T' ⟶ T` over `Spec R` and a `T`-point `x` of `A`, is the `T'`-point
  `ψ ≫ x` (`schemeHomOverComp_coe`).
- A `RelativeGroupLaw R f` consists of, for every `T ⟶ Spec R`, a multiplication, a unit and an inverse on
  the set of `T`-points `SchemeHomOver t f`, satisfying associativity, left and right unit laws and
  `inv x * x = 1`, with multiplication natural in `T` (`mul_natural`). By Yoneda this amounts to a group
  scheme structure on `A` over `Spec R`, given on points.
- `G.IsCommutative` means the multiplication is commutative on all `T`-points
  (`IsCommutative.mul_comm`).
- `G.pointGroup t` is the resulting `Group` structure on the `T`-points. `RelativeGroupLaw.mul_inv_cancel`
  derives `x * inv x = 1`, and `RelativeGroupLaw.one_natural` shows that the unit is natural in `T`.
- `trivialRelativeGroupLaw R` is the unique group law on `𝟙 (Spec R)` (each set of points has one
  element). `relativeGroupLaw_pointwise_eq_of_isIso` shows that any two group laws on an isomorphism
  `f` agree.

## Provenance and licence

This file is a port of `Definitions/Def_AlgebraicGeometry_RelativeGroupLaw.lean` from the Anthropic Lean
formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026
Anthropic, PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE`
and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. Declaration names and namespaces are FLT's. The port makes only these
changes:

- an attribution header is added above the imports;
- the import of the FLT module `Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier` is
  renamed to `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`.
