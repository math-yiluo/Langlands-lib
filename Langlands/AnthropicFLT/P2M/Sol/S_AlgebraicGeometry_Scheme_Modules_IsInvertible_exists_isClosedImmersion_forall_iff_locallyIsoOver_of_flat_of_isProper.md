# Seesaw for pairs of invertible sheaves over a noetherian base

`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isClosedImmersion_forall_iff_locallyIsoOver_of_flat_of_isProper` proves the theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isClosedImmersion_forall_iff_locallyIsoOver_of_flat_of_isProper.solution`. Its statement is that of `AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isClosedImmersion_forall_iff_locallyIsoOver_of_flat_of_isProper`, which `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isClosedImmersion_forall_iff_locallyIsoOver_of_flat_of_isProper` states under its FLT name. This is the seesaw theorem used by the Library's
`Langlands.AlgebraicGeometry.Picard.noetherianLineBundleSeesaw`.

## Statement

Let `R` be a commutative ring in universe `u` and `c : X ⟶ Spec R` a proper,
flat, geometrically integral morphism such that for every `R`-algebra `B` the
second projection `X ×_{Spec R} Spec B ⟶ Spec B` is bijective on global
functions (`appTop`). Let `T` be a locally noetherian scheme with a morphism
`t : T ⟶ Spec R`, write `X_T = X ×_{Spec R} T`, and let `M`, `M'` be invertible
sheaves of modules on `X_T` (the port's `Scheme.Modules.IsInvertible`). Then
there is a closed immersion `ι : Z ⟶ T` with the following property: a
morphism `ψ : T' ⟶ T` factors through `ι` if and only if the pullbacks of `M`
and `M'` to `X_T ×_T T'` are isomorphic locally over `T'`
(`Scheme.Modules.LocallyIsoOver`, from the FLT module
`Definitions/Def_GoodReductionJacobian_RelativeGroupLawTranslate`: every
point of `T'` has an open neighbourhood `U` such that the two pullbacks are
isomorphic on the preimage of `U`).

## Provenance and licence

The Lean file is ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isClosedImmersion_forall_iff_locallyIsoOver_of_flat_of_isProper.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed, and its commands are replaced by the equivalent standard Lean commands: `p2m_open` by `open` (with `hiding` where it hid names); a command left with nothing to open or export is dropped. No declaration, statement or proof step changed;

## Proof outline

Write `dual` for the internal hom into the structure sheaf. Put
`N = M ⊗ dual M'` and `Ninv = dual N`; both are invertible
(`IsInvertible.tensor_monoidalV2`, `IsInvertible.dual_monoidalV2`). The proof
applies the version for one sheaf against the structure sheaf,
`Scheme.Modules.IsInvertible.exists_isClosedImmersion_forall_iff_locallyIsoOver_unit_of_flat_of_isProper`
(in this port), to `N` and `Ninv`, and checks its two extra hypotheses.

1. If the pullback of `N` along some morphism `g` is trivial, so is that of
   `Ninv`: `g^* (dual N) ≅ dual (g^* N)`
   (`IsInvertible.pullback_dual_monoidalV2`), the dual of an isomorphism is an
   isomorphism, and the dual of the structure sheaf is the structure sheaf.
2. Let `k : Spec K ⟶ T` be a point with values in a field `K`, and `Y` the
   fibre `X_T ×_T Spec K`, with `g : Y ⟶ X_T`. Suppose `g^* N` and `g^* Ninv`
   have nonzero global sections. Pasting pullback squares identifies `Y` with
   the base change of `c` along `k ≫ t`, so `Y` is integral by geometric
   integrality, and, with `K` an `R`-algebra through `k ≫ t`, the global
   functions of `Y` are `K` by the hypothesis on `c`; hence every nonzero
   global function is a unit. A nonzero section of `g^* Ninv` gives one of
   `dual (g^* N)`, and
   `Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_section_ne_zero_of_dual_section_ne_zero`
   (in this port) shows that `g^* N` is trivial.

The unit version gives `ι : Z ⟶ T` such that `ψ` factors through `ι` iff the
pullback of `N` is locally over `T'` isomorphic to the structure sheaf. It
remains to compare this with the condition for `M` and `M'`. Pullback is
monoidal and commutes with duals of invertible sheaves, so the pullback of
`N` is isomorphic to `g^* M ⊗ dual (g^* M')`. For sheaves `A`, `B` with `B`
invertible, `A ≅ B` on an open if and only if `A ⊗ dual B ≅ 𝟙` there: in one
direction tensor the isomorphism with `dual B` and use `B ⊗ dual B ≅ 𝟙`; in
the other, `A ≅ A ⊗ (dual B ⊗ B) ≅ (A ⊗ dual B) ⊗ B ≅ B`. Applying this on the
preimages of opens of `T'` (where the restriction of `B` is again invertible
and restriction is monoidal) gives the equivalence of the two local
conditions.
