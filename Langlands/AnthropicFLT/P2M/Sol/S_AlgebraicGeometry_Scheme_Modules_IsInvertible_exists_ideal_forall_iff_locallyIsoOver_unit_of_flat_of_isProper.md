# Seesaw against the structure sheaf over a noetherian affine base

`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ideal_forall_iff_locallyIsoOver_unit_of_flat_of_isProper` proves the theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ideal_forall_iff_locallyIsoOver_unit_of_flat_of_isProper.solution`. Its statement is that of `AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_ideal_forall_iff_locallyIsoOver_unit_of_flat_of_isProper`, which `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ideal_forall_iff_locallyIsoOver_unit_of_flat_of_isProper` states under its FLT name.

## Statement

Let `A` be a noetherian commutative ring in universe `u` and
`c : X ⟶ Spec A` a proper flat morphism such that for every `A`-algebra `B`
the second projection `X ×_{Spec A} Spec B ⟶ Spec B` is bijective on global
functions. Let `N` and `Ninv` be invertible sheaves of modules on `X` (the
port's `Scheme.Modules.IsInvertible`) such that

- for every field `K` that is an `A`-algebra, if the pullbacks of `N` and of
  `Ninv` to the fibre `X_K` both have nonzero global sections, then the
  pullback of `N` to `X_K` is trivial; and
- for every morphism `g : Y ⟶ X`, if `g^* N` is trivial then so is
  `g^* Ninv`.

Then there is an ideal `I` of `A` such that a morphism `ψ : T' ⟶ Spec A`
factors through the closed subscheme `Spec (A / I)` if and only if the
pullback of `N` to `X ×_{Spec A} T'` is locally over `T'` isomorphic to the
structure sheaf (`Scheme.Modules.LocallyIsoOver`).

## Provenance and licence

The Lean file is ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ideal_forall_iff_locallyIsoOver_unit_of_flat_of_isProper.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed, and its commands are replaced by the equivalent standard Lean commands: `p2m_open` by `open` (with `hiding` where it hid names); a command left with nothing to open or export is dropped. No declaration, statement or proof step changed;

## Proof outline

For an `A`-algebra `B`, write `F(B)` for the condition that the pullback of
`N` to `X_B` is locally over `Spec B` isomorphic to the structure sheaf, and
more generally `F(ψ)` for a morphism `ψ : T' ⟶ Spec A`.

1. Stability. `F` is stable under base change: if it holds for `ψ`, it holds
   for `z ≫ ψ` (`lio_baseChange`, `lio_precomp`, with the pullback-pasting
   isomorphisms `pullbackLeftPullbackSndIso`). In particular `F(B)` implies
   `F(C)` for a `B`-algebra `C` (`falg_of_tower`). Conversely, `F(B)` holds if
   it holds for the localizations `B_{h_i}` at a family of elements of `A`
   whose images do not all lie in any prime of `B`: the open immersions
   `Spec B_{h_i} → Spec B` and the corresponding open pieces of `X_B` transport
   the local isomorphisms (`exists_iso_of_openImmersion`, `falg_of_cover`).
2. Local representability.
   `Scheme.Modules.IsInvertible.exists_ideal_forall_locallyIsoOver_unit_iff_map_eq_bot`
   (in this port) gives, for each prime `𝔭` of `A`, an element `h ∉ 𝔭` and an
   ideal `J` with `F(B) ↔ J B = 0` for every `A`-algebra `B` in which `h` is a
   unit.
3. Gluing the ideals (`exists_ideal_repr`). The elements `h` generate the unit
   ideal, so finitely many `h_1, …, h_k` with ideals `J_1, …, J_k` suffice. On
   overlaps, `J_i A_{h_i h_k} ⊆ J_k A_{h_i h_k}`: over the quotient of
   `A_{h_i h_k}` by `J_k`, `F` holds by the description for `k`, so `J_i`
   vanishes there by the description for `i`. Put
   `I = ⋂_i (J_i A_{h_i} ∩ A)`. If `F(B)`, then for every prime of `B` some
   `h_i` is a unit near it, `J_i` vanishes on `B_{h_i}` by step 1, and every
   element of `I` is killed by a power of `h_i` in `B`; an element killed
   locally at every prime is zero, so `I B = 0`. Conversely, if `I B = 0`, then
   for each `i` and `j ∈ J_i`, a large power `h_i ^ n j` lies in `I` by the
   overlap inclusions, so `J_i B_{h_i} = 0`, `F(B_{h_i})` holds, and `F(B)`
   follows from the cover property of step 1.
4. From algebras to schemes (`F_iff_of_repr`). If `ψ` factors through
   `Spec (A / I)`, then `F(A / I)` holds because `I (A / I) = 0`, and `F(ψ)`
   follows by stability. Conversely, if `F(ψ)` holds, then for every affine
   open `W` of `T'` the ring `Γ(T', W)` is an `A`-algebra through `ψ` with
   `F(Γ(T', W))`, so `I` maps to zero in `Γ(T', W)`. The affine opens cover
   `T'`, so `I` maps to zero in `Γ(T', ⊤)`, the map `A → Γ(T', ⊤)` factors
   through `A / I`, and `ψ` factors through `Spec (A / I)` via
   `T' ⟶ Spec Γ(T', ⊤)` (`Scheme.toSpecΓ`).
