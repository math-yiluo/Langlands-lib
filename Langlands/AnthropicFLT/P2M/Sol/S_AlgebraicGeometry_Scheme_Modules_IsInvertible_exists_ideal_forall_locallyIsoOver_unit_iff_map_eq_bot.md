# Local representability of triviality of an invertible sheaf over a noetherian affine base

`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ideal_forall_locallyIsoOver_unit_iff_map_eq_bot` proves the theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ideal_forall_locallyIsoOver_unit_iff_map_eq_bot.solution`. Its statement is that of `AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_ideal_forall_locallyIsoOver_unit_iff_map_eq_bot`, which `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ideal_forall_locallyIsoOver_unit_iff_map_eq_bot` states under its FLT name.

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

The Lean file is ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ideal_forall_locallyIsoOver_unit_iff_map_eq_bot.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed, and its commands are replaced by the equivalent standard Lean commands: `p2m_open` by `open` (with `hiding` where it hid names); a command left with nothing to open or export is dropped. No declaration, statement or proof step changed;

## Proof outline

Write `F(B)` for the local triviality condition and `κ` for the residue field
of `𝔭`. By `Scheme.Modules.exists_twoTermComplex_sectionsEquiv_forall_baseChange`
(in this port) there are two-term complexes `G` and `G'` of finite free
`A`-modules with `Γ(N_B) ≅ G.H0 B` and `Γ(Ninv_B) ≅ G'.H0 B` for every `B`.
For a field `K`, the global functions of `X_K` are `K`, so nonzero ones are
units; and if `N_C` is trivial then `Γ(N_C) ≅ Γ(𝒪_{X_C}) ≅ C`
(`secEquivOfIsoUnit`).

**Case 1: `N_κ` is trivial** (`caseT`). Then `G.H0 κ ≅ κ`, so
`G.fibreH0 𝔭 = 1`, and
`CoherentBaseChange.TwoTermComplex.exists_nonempty_H0_linearEquiv_annihilator_of_fibreH0_le_one`
(in this port) gives `h₁ ∉ 𝔭` and `J` with `G.H0 B ≅ Ann_B(J B)` whenever `h₁`
is a unit in `B`. An ideal whose annihilator is free of rank one is zero
(`ideal_eq_bot_of_annihilator_equiv`); in particular `J κ = 0`.

- `F(B) → J B = 0` (`map_eq_bot_of_locallyIsoOver`): `F(B)` gives, near every
  prime of `B`, a basic open `D(g)` over which `N` is trivial
  (`exists_away_iso_unit`). Then `Ann(J B_g) ≅ Γ(N_{B_g}) ≅ B_g`, so
  `J B_g = 0`, and every element of `J B`, being locally zero at every prime,
  is zero (`eq_zero_of_forall_prime`).
- The converse. Let `B₀ = (A / J)_{h₁}`. Over every `B₀`-algebra `C`,
  `J C = 0`, so `Γ(N_C) ≅ Ann(0) = C`. The map `B₀ → κ` has prime kernel `𝔭₀`,
  and `N` is trivial on the fibre over the residue field of `𝔭₀`, pulled back
  from `N_κ` along `κ → κ(𝔭₀)` (`isoUnitOfAlgHom`). So
  `Scheme.Modules.IsInvertible.exists_nonempty_pullback_preimage_basicOpen_iso_unit_of_forall_sections_linearEquiv`
  (in this port) applies to `X_{B₀}` and gives `g ∈ B₀ \ 𝔭₀` such that `N` is
  trivial over the preimage of `D(g)`; hence `N_B` is trivial for every
  `B₀`-algebra `B` in which `g` is a unit (`caseT_core`). Write
  `g = a / h₁ ^ n` with `a ∈ A`; then `a ∉ 𝔭`. Put `h = h₁ a`. If `h` is a unit
  in `B` and `J B = 0`, then `B` is a `B₀`-algebra in which `g` is a unit, so
  `N_B` is trivial and `F(B)` holds.

**Case 2: `N_κ` is not trivial.** By the fibre hypothesis, `Γ(N_κ) = 0` or
`Γ(Ninv_κ) = 0`, so `G.fibreH0 𝔭 = 0` or `G'.fibreH0 𝔭 = 0`. In the first case
(`exists_forall_subsingleton_of_fibreH0_eq_zero`) the annihilator description
gives `h' ∉ 𝔭` and `J'` with `Ann(J' κ) = 0`, so some `j ∈ J'` is not in `𝔭`.
If `h' j` is a unit in `B`, then `J' C = C` and hence `Γ(N_C) = 0` for every
localization `C` of `B`. If moreover `F(B)` holds and `B ≠ 0`, some prime `𝔮`
of `B` has a basic open neighbourhood `D(g)` over which `N` is trivial, so
`B_g ≅ Γ(N_{B_g}) = 0`, contradicting `g ∉ 𝔮`. Hence `F(B)` forces `B = 0`. In the second case the same argument applies to `Ninv`, using
that `F(B)` for `N` implies it for `Ninv` by the second hypothesis
(`locallyIsoOver_inv`). Taking `J = A`, `F(B)` holds iff `B = 0` iff `J B = 0`:
for `B = 0` the condition `F(B)` is vacuous because `Spec B` is empty.
