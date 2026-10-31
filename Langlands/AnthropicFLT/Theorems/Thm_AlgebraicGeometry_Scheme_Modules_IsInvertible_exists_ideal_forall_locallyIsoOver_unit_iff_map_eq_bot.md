# Local representability of triviality of an invertible sheaf over a noetherian affine base

`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ideal_forall_locallyIsoOver_unit_iff_map_eq_bot` proves the theorem `AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_ideal_forall_locallyIsoOver_unit_iff_map_eq_bot`.

## Statement

Let `A` be a noetherian commutative ring in universe `u` and
`c : X ⟶ Spec A` a proper flat morphism such that for every `A`-algebra `B`
the second projection `X_B = X ×_{Spec A} Spec B ⟶ Spec B` is bijective on
global functions. Let `N`, `Ninv` be invertible sheaves of modules on `X` (the
port's `Scheme.Modules.IsInvertible`) such that

- for every field `K` that is an `A`-algebra, if the pullbacks of `N` and
  `Ninv` to `X_K` both have nonzero global sections, the pullback of `N` to
  `X_K` is trivial; and
- for every morphism `g : Y ⟶ X`, if `g^* N` is trivial then so is
  `g^* Ninv`.

Then for every prime `𝔭` of `A` there are `h ∈ A` with `h ∉ 𝔭` and an ideal
`J` of `A` such that for every `A`-algebra `B` in which `h` is a unit, the
pullback `N_B` of `N` to `X_B` is locally over `Spec B` isomorphic to the
structure sheaf (`Scheme.Modules.LocallyIsoOver`) if and only if `J B = 0`.

## Provenance and licence

The Lean file is ported from `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ideal_forall_locallyIsoOver_unit_iff_map_eq_bot.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util` is removed, and the proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ideal_forall_locallyIsoOver_unit_iff_map_eq_bot.solution` is written `by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ideal_forall_locallyIsoOver_unit_iff_map_eq_bot.solution` applied to the theorem's binders in order (`_` for anonymous instance binders). The statement is unchanged;

## Proof

The proof applies `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ideal_forall_locallyIsoOver_unit_iff_map_eq_bot.solution` from `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ideal_forall_locallyIsoOver_unit_iff_map_eq_bot`, which has the same statement. The Markdown of that module outlines the argument.
