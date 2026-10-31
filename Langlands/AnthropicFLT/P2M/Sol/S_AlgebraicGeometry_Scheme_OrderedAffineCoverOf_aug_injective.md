# The augmentation of the Čech complex of an ordered affine cover is injective

`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_aug_injective` proves the theorem `P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_aug_injective.solution`. Its statement is that of `AlgebraicGeometry.Scheme.OrderedAffineCoverOf.aug_injective`, which `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_aug_injective` states under its FLT name.

## Statement

Let `R` be a commutative ring, `V` a scheme with a morphism
`π : V ⟶ Spec R`, `W` an open of `V` and `K` an ordered affine cover of `W`
(the FLT structure `Scheme.OrderedAffineCoverOf W`: a finite linearly ordered
family of affine opens `K.U i ≤ W` whose supremum is `W`). The sections of the
structure sheaf are `R`-modules through `π`
(`Scheme.OrderedAffineCoverOf.moduleSections π`). Then the augmentation
`K.aug π : Γ(V, W) →ₗ[R] K.cochain 0`, which sends a section over `W` to the
family of its restrictions to the opens `K.inter σ` of the `0`-simplices `σ`,
is injective.

## Provenance and licence

The Lean file is ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_aug_injective.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed, and its commands are replaced by the equivalent standard Lean commands: `p2m_export` by `export`, `p2m_open` by `open` (with `hiding` where it hid names); a command left with nothing to open or export is dropped. No declaration, statement or proof step changed;

## Proof outline

For each index `i` of the cover, the constant map `0 ↦ i` is a `0`-simplex
`σ` (strictly monotone because `Fin 1` has one element) with
`K.inter σ = K.U i`. Hence the opens `K.inter σ`, for `σ` a `0`-simplex,
cover `W`. If two sections over `W` have the same image under the
augmentation, they agree on each member of this cover, so they are equal
because the structure sheaf is a sheaf (`TopCat.Sheaf.eq_of_locally_eq'`).
