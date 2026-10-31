# Seesaw for pairs of invertible sheaves over a noetherian base

`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isClosedImmersion_forall_iff_locallyIsoOver_of_flat_of_isProper` proves the theorem `AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isClosedImmersion_forall_iff_locallyIsoOver_of_flat_of_isProper`.

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

The Lean file is ported from `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isClosedImmersion_forall_iff_locallyIsoOver_of_flat_of_isProper.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util` is removed, and the proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isClosedImmersion_forall_iff_locallyIsoOver_of_flat_of_isProper.solution` is written `by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isClosedImmersion_forall_iff_locallyIsoOver_of_flat_of_isProper.solution` applied to the theorem's binders in order (`_` for anonymous instance binders). The statement is unchanged;

## Proof

The proof applies `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isClosedImmersion_forall_iff_locallyIsoOver_of_flat_of_isProper.solution` from `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isClosedImmersion_forall_iff_locallyIsoOver_of_flat_of_isProper`, which has the same statement. The Markdown of that module outlines the argument.
