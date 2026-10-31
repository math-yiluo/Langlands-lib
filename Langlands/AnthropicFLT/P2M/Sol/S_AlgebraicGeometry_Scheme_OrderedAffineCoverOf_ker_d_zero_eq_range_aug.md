# Exactness of the Čech complex of an ordered affine cover in degree zero

`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug` proves the theorem `P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug.solution`. Its statement is that of `AlgebraicGeometry.Scheme.OrderedAffineCoverOf.ker_d_zero_eq_range_aug`, which `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug` states under its FLT name.

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

The Lean file is ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed, and its commands are replaced by the equivalent standard Lean commands: `p2m_export` by `export`, `p2m_open` by `open` (with `hiding` where it hid names); a command left with nothing to open or export is dropped. No declaration, statement or proof step changed;

## Proof outline

The proof first sets up combinatorics of simplices: a simplex is determined
by its image, a finite set of indices (`altIdx_eq_of_altImg`); the image of a
face is the image with one index erased (`altImg_altFace`); and indices can be
inserted at the right position (`altInsert`, `insPos`). In degree zero a
simplex is a single index.

- Range in kernel: for `w ∈ Γ(V, W)` and a `1`-simplex `(a, b)`, the
  differential of `aug w` is the difference of two restrictions of `w` to
  `U_a ∩ U_b`, which is zero.
- Kernel in range: let `z` be a `0`-cochain with `d z = 0`. For indices
  `a < b`, the component of `d z` at the `1`-simplex `(a, b)` is
  `z_b|U_a∩U_b - z_a|U_a∩U_b`, so `z_a` and `z_b` agree on the overlap; for
  `a > b` swap the roles, and for `a = b` there is nothing to prove. So `z`
  is a compatible family on the cover `{U_i}` of `W` (each `U_i` is the open
  of the `0`-simplex `i`), and it glues to a section `w` over `W`
  (`TopCat.Sheaf.existsUnique_gluing'`) with `aug w = z`.
