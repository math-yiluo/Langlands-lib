# Seesaw against the structure sheaf over a locally noetherian base

`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isClosedImmersion_forall_iff_locallyIsoOver_unit_of_flat_of_isProper` proves the theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isClosedImmersion_forall_iff_locallyIsoOver_unit_of_flat_of_isProper.solution`. Its statement is that of `AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isClosedImmersion_forall_iff_locallyIsoOver_unit_of_flat_of_isProper`, which `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isClosedImmersion_forall_iff_locallyIsoOver_unit_of_flat_of_isProper` states under its FLT name.

## Statement

Let `R` be a commutative ring in universe `u` and `c : X ⟶ Spec R` a proper
flat morphism such that for every `R`-algebra `B` the second projection
`X ×_{Spec R} Spec B ⟶ Spec B` is bijective on global functions. Let `T` be a
locally noetherian scheme with `t : T ⟶ Spec R`, write `X_T = X ×_{Spec R} T`,
and let `N`, `Ninv` be invertible sheaves of modules on `X_T` (the port's
`Scheme.Modules.IsInvertible`) such that

- for every field `K` and point `k : Spec K ⟶ T`, if the pullbacks of `N` and
  `Ninv` to the fibre `X_T ×_T Spec K` both have nonzero global sections, the
  pullback of `N` to that fibre is trivial; and
- for every morphism `g : Y ⟶ X_T`, if `g^* N` is trivial then so is
  `g^* Ninv`.

Then there is a closed immersion `ι : Z ⟶ T` such that a morphism
`ψ : T' ⟶ T` factors through `ι` if and only if the pullback of `N` to
`X_T ×_T T'` is locally over `T'` isomorphic to the structure sheaf
(`Scheme.Modules.LocallyIsoOver`).

## Provenance and licence

The Lean file is ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isClosedImmersion_forall_iff_locallyIsoOver_unit_of_flat_of_isProper.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed, and its commands are replaced by the equivalent standard Lean commands: `p2m_open` by `open` (with `hiding` where it hid names); a command left with nothing to open or export is dropped. No declaration, statement or proof step changed;

## Proof outline

Write `F(ψ)` for the condition on `ψ : T' ⟶ T` in the statement.

1. Formal properties of `F`. It is stable under composition, `F(ψ)` implies
   `F(z ≫ ψ)` (`F_comp`), and it is local on the source: `F(ψ)` holds if it
   holds on the members of an open cover of `T'` (`F_of_openCover`). Both are
   checked with the pullback-pasting isomorphisms and by transporting local
   isomorphisms along open immersions.
2. Affine charts. For an affine open `U` of `T`, the ring `Γ(T, U)` is
   noetherian and an `R`-algebra through `t`. Identify
   `X_T ×_T Spec Γ(T, U)` with `X ×_{Spec R} Spec Γ(T, U)` (`mU`, `πU`, `eU`),
   and pull `N` and `Ninv` back to it. The hypotheses transfer: the global
   functions condition by the pullback-pasting isomorphism `θ`, the fibre
   condition by composing field points with `U.fromSpec`, and the condition on
   `Ninv` by composing with `mU`.
   `Scheme.Modules.IsInvertible.exists_ideal_forall_iff_locallyIsoOver_unit_of_flat_of_isProper`
   (in this port) gives an ideal `I_U` of `Γ(T, U)` such that, for
   `ψ' : T' ⟶ Spec Γ(T, U)`, `F(ψ' ≫ U.fromSpec)` holds iff `ψ'` factors
   through `Spec (Γ(T, U) / I_U)`, that is, iff `I_U` maps to zero in
   `Γ(T', ⊤)` (`exists_fac_iff`). Call this property `KI U I_U`.
3. The ideal sheaf. The ideal with property `KI U` is unique (`KI_unique`):
   `F` holds over `Spec (Γ(T, U) / I)`, so the other ideal maps to zero there.
   If `KI U I` holds, then `KI` holds on a basic open `D(f) ⊆ U` for the image
   of `I` in `Γ(T, D(f))` (`KI_basicOpen`, via
   `IsAffineOpen.map_fromSpec`). So the ideals `I_U` are compatible with
   restriction to basic opens and form Mathlib's `Scheme.IdealSheafData` on
   `T` (`idealSheaf`).
4. The closed subscheme. Let `Z` be the closed subscheme of this ideal sheaf
   and `ι` its inclusion, a closed immersion. If `ψ` factors through `ι`, then
   `F(ψ)` follows by step 1 from `F(ι)`, which holds on the affine cover of `Z`
   by the charts `Spec (Γ(T, U) / I_U)`. Conversely, if `F(ψ)`, then for every
   affine open `U` of `T` and every affine open `V ⊆ ψ⁻¹ U` of `T'`, step 2
   applied to `Spec Γ(T', V) ⟶ Spec Γ(T, U)` (`IsAffineOpen.SpecMap_appLE_fromSpec`)
   shows that `I_U` maps to zero in `Γ(T', V)`; these opens cover `ψ⁻¹ U`, so
   the ideal sheaf is contained in the kernel of `ψ`, and `ψ` factors through
   `ι` (`IsClosedImmersion.lift`).
