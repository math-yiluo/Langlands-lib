# The augmentation of the Čech complex of an ordered affine cover is injective

`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_aug_injective` proves the theorem `AlgebraicGeometry.Scheme.OrderedAffineCoverOf.aug_injective`.

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

The Lean file is ported from `Theorems/Thm_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_aug_injective.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util` is removed, and the proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_aug_injective.solution` is written `by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_aug_injective.solution` applied to the theorem's binders in order (`_` for anonymous instance binders). The statement is unchanged;

## Proof

The proof applies `P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_aug_injective.solution` from `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_aug_injective`, which has the same statement. The Markdown of that module outlines the argument.
