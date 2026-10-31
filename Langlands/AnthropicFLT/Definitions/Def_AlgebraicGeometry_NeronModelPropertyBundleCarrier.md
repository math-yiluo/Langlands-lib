# The Néron mapping property over a Dedekind base

Module `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier`, in
namespace `NeronModelInfra`. Schemes and rings live in a fixed universe `u`.

## Definitions and results

Let `R` be a commutative ring and `K` a field with an `R`-algebra structure (later `R` a Dedekind domain
and `K` its fraction field).

- `specGenericFibreInclusion R K : Spec K ⟶ Spec R` is the morphism induced by `R → K`
  (`specGenericFibreInclusion_eq`).
- `SchemeHomOver g f`, for `g : Y ⟶ B` and `f : X ⟶ B`, is the type of morphisms `φ : Y ⟶ X` over `B`
  (`φ ≫ f = g`).
- `genericFibreRestrict R K f g φ`, for `f : X ⟶ Spec R`, `g : Y ⟶ Spec R` and `φ` over `Spec R`, is the
  base change of `φ` to the generic fibres `Y_K ⟶ X_K`, a morphism over `Spec K`
  (`genericFibreRestrict_coe_comp_snd`, `genericFibreRestrict_coe_comp_fst`; by
  `genericFibreRestrict_coe_eq_pullbackMap` it is the pullback map).
- `NeronUniqueExtension R K f` (the Néron mapping property): for every smooth `t : T ⟶ Spec R`,
  restriction to generic fibres is a bijection from morphisms `T ⟶ X` over `Spec R` to morphisms
  `T_K ⟶ X_K` over `Spec K` (`neronUniqueExtension_iff_bijective`).
- `NeronModelPropertyBundle R K f`, for a Dedekind domain `R` with fraction field `K`: `f` is smooth,
  separated, locally of finite type and quasi-compact, and has the Néron mapping property. So `X` is a
  Néron model of its generic fibre, without a group structure. The theorems
  `NeronModelPropertyBundle.smooth_mathlibSpelling`, `isSeparated_mathlibSpelling`,
  `locallyOfFiniteType_mathlibSpelling`, `quasiCompact_mathlibSpelling`, `neronMapping_bijective` and
  `neronModelPropertyBundle_iff_propertyList` unpack it, and `existsUnique_extension` gives the unique
  extension of a generic-fibre morphism.

**Checks.**

- If `f` is an isomorphism, morphisms over it are unique and exist (`subsingleton_schemeHomOver_of_isIso`,
  `nonempty_schemeHomOver_of_isIso`), so `genericFibreRestrict` is bijective
  (`genericFibreRestrict_bijective_of_isIso`) and `f` has the Néron mapping property
  (`neronUniqueExtension_of_isIso`). In particular `𝟙 (Spec R)` is a Néron model
  (`neronModelPropertyBundle_id`), for instance over `ℤ_p` (`gate_neronModelPropertyBundle_trivialGroupScheme_zp`,
  and `…_z3` for `p = 3`).
- The generic point `Spec ℚ_p ⟶ Spec ℤ_p` has no section over `Spec ℤ_p`
  (`isEmpty_schemeHomOver_id_specGenericFibreInclusion_zp`: `p` would become a unit in `ℤ_p`), so it
  fails the Néron mapping property (`gate_neronUniqueExtension_fails_genericFibreOnly`, and `…_three`)
  and is not a Néron model (`gate_neronModelPropertyBundle_not_genericFibreOnly`).

The file ends with `#guard_msgs in #print axioms …` commands for twelve of these theorems. They check
that each depends only on `propext`, `Classical.choice` and `Quot.sound`, and declare nothing.

## Provenance and licence

This file is a port of `Definitions/Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier.lean` from the
Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md`
are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice
applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`.

The file imports only Mathlib, so its imports are unchanged.
