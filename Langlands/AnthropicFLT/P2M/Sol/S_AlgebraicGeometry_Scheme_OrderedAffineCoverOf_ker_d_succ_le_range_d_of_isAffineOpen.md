# The Čech complex of an ordered affine cover of an affine open is exact in positive degrees

`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_succ_le_range_d_of_isAffineOpen` proves the theorem `P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_succ_le_range_d_of_isAffineOpen.solution`. Its statement is that of `AlgebraicGeometry.Scheme.OrderedAffineCoverOf.ker_d_succ_le_range_d_of_isAffineOpen`, which `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_succ_le_range_d_of_isAffineOpen` states under its FLT name.

## Statement

Let `R` be a commutative ring, `V` a scheme with a separated morphism
`π : V ⟶ Spec R`, `W` an affine open of `V` and `K` an ordered affine cover of
`W` (the FLT structure `Scheme.OrderedAffineCoverOf W`: a finite linearly
ordered family of affine opens `K.U i ≤ W` whose supremum is `W`). Sections of
the structure sheaf are `R`-modules through `π`. Then the alternating Čech
complex of `K` with coefficients in the structure sheaf is exact in positive
degrees: for every `p`, `ker (K.d π (p + 1)) ≤ range (K.d π p)`.

## Provenance and licence

The Lean file is ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_succ_le_range_d_of_isAffineOpen.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed, and its commands are replaced by the equivalent standard Lean commands: `p2m_export` by `export`, `p2m_open` by `open` (with `hiding` where it hid names); a command left with nothing to open or export is dropped. No declaration, statement or proof step changed;

## Proof outline

The combinatorics of simplices (strictly increasing tuples of indices,
determined by their images; faces erase an index, `altInsert` inserts one) is
the same as in `Scheme.OrderedAffineCoverOf.ker_d_zero_eq_range_aug`.

1. Covers containing the whole open (`wholeSpace_exact`). If some member
   `K.U i₀` equals `W`, inserting `i₀` into a simplex does not change its open
   (`altOpen_altInsert`). The map `htpy` sends a cochain `z` to the cochain
   whose value at a simplex `σ` not containing `i₀` is `± z(σ ∪ {i₀})`, with
   the sign given by the position of `i₀`, and zero otherwise. It is a
   contracting homotopy: `d ∘ htpy + htpy ∘ d = id` in positive degrees
   (`htpy_rel`), so every cocycle is a coboundary.
2. Intersections are affine (`isAffineOpen_altOpen`): since `π` is separated,
   intersections of affine opens are affine
   (`isAffineOpen_inf_of_isSeparated`).
3. Localization at basic opens. Let `f ∈ Γ(V, W)` with `D(f) ⊆ K.U i₀`. The
   cover `K` restricted to `D(f)` (`restrictBasic`, with members
   `K.U i ∩ D(f)`) contains the whole open `D(f)` as the member `i₀`, so its
   complex is exact by step 1. The opens of its simplices are the basic opens
   of the restriction of `f` in the affine opens of `K`, so their sections are
   localizations at `f` (`away_surj`, `away_ker`). Restricting a cocycle `z` of
   `K`, writing the restriction as a coboundary, and clearing denominators
   shows that `f ^ N • z` is a coboundary of `K` for some `N`
   (`smul_pow_mem_range`). Here the coboundaries form a `Γ(V, W)`-submodule
   (`rangeW`), because the differential is linear over functions on `W`.
4. Since `W` is affine, functions `f` with `D(f)` inside some member of the
   cover generate the unit ideal of `Γ(V, W)` (`exists_refinement`, via
   `IsAffineOpen.exists_basicOpen_le`). A vector some power of each of whose
   multiples by such generators lies in a submodule lies in it
   (`Submodule.mem_of_span_eq_top_of_smul_pow_mem`), so every cocycle `z` of
   positive degree is a coboundary.
