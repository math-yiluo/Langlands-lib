# An invertible sheaf with universally free rank-one sections and a trivial fibre is trivial near that fibre

`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_nonempty_pullback_preimage_basicOpen_iso_unit_of_forall_sections_linearEquiv` proves the theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_nonempty_pullback_preimage_basicOpen_iso_unit_of_forall_sections_linearEquiv.solution`. Its statement is that of `AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_nonempty_pullback_preimage_basicOpen_iso_unit_of_forall_sections_linearEquiv`, which `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_nonempty_pullback_preimage_basicOpen_iso_unit_of_forall_sections_linearEquiv` states under its FLT name.

## Statement

Let `R` be a noetherian commutative ring in universe `u`, `f : Y ⟶ Spec R` a
proper flat morphism and `P` an invertible sheaf of modules on `Y` (the port's
`Scheme.Modules.IsInvertible`: locally isomorphic to the structure sheaf).
For an `R`-algebra `C`, write `Y_C = Y ×_{Spec R} Spec C` and `P_C` for the
pullback of `P` along the first projection `Y_C ⟶ Y`; global sections are
modules over `R`, respectively `C`, through `f` and the second projection
(`Scheme.TwoAffineOpenCover.moduleSectionsOfHom`). Assume:

- the global sections of `P` are a free `R`-module of rank one, and for every
  `R`-algebra `C` the global sections of `P_C` are a free `C`-module of rank
  one;
- `𝔭` is a prime of `R` with residue field `K`, every nonzero global function
  on the fibre `Y_K` is a unit, and `P_K` is isomorphic to the structure sheaf
  of `Y_K`.

Then there is `g ∈ R` with `g ∉ 𝔭` such that the pullback of `P` to the open
`f⁻¹(D(g))` is isomorphic to its structure sheaf.

## Provenance and licence

The Lean file is ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_nonempty_pullback_preimage_basicOpen_iso_unit_of_forall_sections_linearEquiv.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed, and its commands are replaced by the equivalent standard Lean commands: `p2m_open` by `open` (with `hiding` where it hid names); a command left with nothing to open or export is dropped. No declaration, statement or proof step changed;

## Proof outline

1. By `Scheme.Modules.exists_twoTermComplex_sectionsEquiv_forall_baseChange`
   (in this port) there is a two-term complex `G` of finite free `R`-modules
   `d : C0 → C1` with `Γ(P) ≅ ker d` and `Γ(P_A) ≅ G.H0 A = ker (A ⊗ d)` for
   every `R`-algebra `A`, compatibly with the base change map
   `m ↦ 1 ⊗ m`. By the hypothesis, `G.H0 C ≅ C` for every `C`.
2. Let `σ` be the generator of `Γ(P)` corresponding to `1 ∈ R` and `g₀ ∈ C0`
   its image. Since `σ` generates `Γ(P)`, every element of `ker d` is an
   `R`-multiple of `g₀`.
   `CoherentBaseChange.TwoTermComplex.one_tmul_ne_zero_of_forall_nonempty_H0_linearEquiv`
   (in this port) then gives `1 ⊗ g₀ ≠ 0` in `K ⊗ C0`. By the compatibility
   of step 1, the pullback `s` of `σ` to `Y_K` (its image under the unit of the
   pullback–pushforward adjunction) is therefore nonzero.
3. Fix an isomorphism `e : P_K ≅ 𝒪_{Y_K}`. Then `e(s)` is a nonzero global
   function, hence a unit `t`. For every open `V` of `Y_K`, the map
   `g ↦ g • s|V` is the composite of multiplication by the unit `t|V` and the
   bijection `e⁻¹` on sections over `V` (using that `e⁻¹` is linear and
   commutes with restriction), so it is bijective.
4. Apply `Scheme.Modules.exists_basicOpen_forall_exists_frame_of_frame_pullback`
   (in this port) to the one-element family `σ` and the residue field `K`,
   whose structure map has kernel `𝔭` (`Ideal.ker_algebraMap_residueField`).
   It gives `g ∉ 𝔭` such that every point over `D(g)` has a neighbourhood
   `U` where `g' ↦ g' • σ|W` is bijective for every open `W ≤ U`.
5. By `Scheme.Modules.bijective_smul_of_forall_exists_bijective_smul` (in
   this port), `σ` is then a frame on `W = f⁻¹(D(g))`
   (`Scheme.Modules.IsFrameOn σ W`), and
   `Scheme.Modules.IsFrameOn.nonempty_pullback_iso_unit` (in this port) gives
   the required isomorphism.
