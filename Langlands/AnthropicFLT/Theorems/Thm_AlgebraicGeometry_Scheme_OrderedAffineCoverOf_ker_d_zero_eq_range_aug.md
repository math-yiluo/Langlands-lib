# Exactness of the Čech complex of an ordered affine cover in degree zero

`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug` proves the theorem `AlgebraicGeometry.Scheme.OrderedAffineCoverOf.ker_d_zero_eq_range_aug`.

## Statement

Let `R` be a commutative ring, `V` a scheme with a morphism
`π : V ⟶ Spec R`, `W` an open of `V` and `K` an ordered affine cover of `W`
(the FLT structure `Scheme.OrderedAffineCoverOf W`: a finite linearly ordered
family of affine opens `K.U i ≤ W` whose supremum is `W`). Sections of the
structure sheaf are `R`-modules through `π`. In the alternating Čech complex
of `K` with coefficients in the structure sheaf (simplices are strictly
increasing tuples of indices, `K.Idx n`), the kernel of the first
differential `K.d π 0` equals the range of the augmentation
`K.aug π : Γ(V, W) → K.cochain 0`.

## Provenance and licence

The Lean file is ported from `Theorems/Thm_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util` is removed, and the proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug.solution` is written `by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug.solution` applied to the theorem's binders in order (`_` for anonymous instance binders). The statement is unchanged;

## Proof

The proof applies `P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug.solution` from `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug`, which has the same statement. The Markdown of that module outlines the argument.
