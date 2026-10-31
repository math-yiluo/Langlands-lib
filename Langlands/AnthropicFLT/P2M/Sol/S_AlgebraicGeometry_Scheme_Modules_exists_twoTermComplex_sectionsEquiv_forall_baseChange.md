# Global sections of a locally trivial module on a proper flat scheme are computed by a two-term complex universally

`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_twoTermComplex_sectionsEquiv_forall_baseChange` proves the theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_twoTermComplex_sectionsEquiv_forall_baseChange.solution`. Its statement is that of `AlgebraicGeometry.Scheme.Modules.exists_twoTermComplex_sectionsEquiv_forall_baseChange`, which `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_twoTermComplex_sectionsEquiv_forall_baseChange` states under its FLT name.

## Statement

Let `R` be a noetherian commutative ring in universe `u`, `f : X ⟶ Spec R` a
proper flat morphism and `M` a locally trivial sheaf of modules on `X`
(every point has an open neighbourhood on which the pullback of `M` is
isomorphic to the structure sheaf). For an `R`-algebra `A`, write `M_A` for
the pullback of `M` to `X_A = X ×_{Spec R} Spec A`; global sections are
modules through `f`, respectively the second projection. Then there is a
two-term complex `G` (the FLT structure `CoherentBaseChange.TwoTermComplex`:
a linear map `d : C0 → C1` of finite free `R`-modules) together with

- an `R`-linear isomorphism `ε₀ : Γ(M) ≅ ker d`, and
- for every `R`-algebra `A`, an `A`-linear isomorphism
  `ε_A : Γ(M_A) ≅ ker (A ⊗ d)` (`G.H0 A`),

compatible with base change: for `m ∈ Γ(M)`, `ε_A` sends the pullback of `m`
(its image under the unit of the pullback–pushforward adjunction) to the
image of `1 ⊗ ε₀(m)` under the natural map `A ⊗ ker d → ker (A ⊗ d)`
(`G.kerBaseChangeHom A`).

## Provenance and licence

The Lean file is ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_twoTermComplex_sectionsEquiv_forall_baseChange.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed, and its commands are replaced by the equivalent standard Lean commands: `p2m_open` by `open` (with `hiding` where it hid names); a command left with nothing to open or export is dropped. No declaration, statement or proof step changed;

## Proof outline

1. Since `f` is quasi-compact and `Spec R` is compact, `X` is compact, so a
   finite subcover of the affine cover of `X`, with any linear order on its
   index set, is an ordered affine cover `𝒰` (`coverOfCompact`).
2. Let `F` be the presheaf of `R`-modules of sections of `M`
   (`OModulePresheaf.ofModules f M`) and `C^•(𝒰, F)` its alternating Čech
   complex. Global sections of `M` are the kernel of the first Čech
   differential: restriction to the members of the cover is injective and its
   image is the set of cocycles, by the sheaf property
   (`OModulePresheaf.d_zero_ofModules_eq_zero_iff_existsUnique`). This gives
   `Γ(M) ≅ H⁰(𝒰, F)` (`sectionsEquivH0`), and likewise over every `X_A` for the
   base-changed cover `𝒰.baseChange f A`.
3. `OModulePresheaf.exists_twoTermComplex_kerMapBaseChange_bijective_ofModules`
   gives a two-term complex `G` of finite free `R`-modules and a map of
   complexes `ι : G → C^•(𝒰, F)` in degrees `0, 1` that induces bijections
   `ker (A ⊗ d) → ker (A ⊗ d⁰_F)` for every `A`. For `A = R` this gives
   `ker d ≅ H⁰(𝒰, F)` (identify `R ⊗ -` with the identity via
   `TensorProduct.lid`, `kerMap_bijective`), and composing with step 2 gives
   `ε₀`.
4. `OModulePresheaf.exists_cochain_baseChange_equiv_of_locallyTrivial`
   identifies `A ⊗ C^i(𝒰, F)` with the Čech cochains of `M_A` for the
   base-changed cover, compatibly with the differentials and with pullback of
   sections. Hence `ker (A ⊗ d⁰_F)` is isomorphic to the kernel of the first
   differential for `M_A`, which by step 2 is `Γ(M_A)`. Composing with the
   bijection of step 3 gives `ε_A`.
5. Compatibility is checked componentwise on the cover: both sides send `m`
   to the family of pullbacks of the restrictions of `m` to the members of the
   cover, using that the unit of the pullback–pushforward adjunction commutes
   with restriction.
