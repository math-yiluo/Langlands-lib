# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_mem_of_isSeparated_of_forall_smoothProperCurve_opens_mem`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_mem_of_isSeparated_of_forall_smoothProperCurve_opens_mem.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_mem_of_isSeparated_of_forall_smoothProperCurve_opens_mem.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_mem_of_isSeparated_of_forall_smoothProperCurve_opens_mem`. Statement. `AlgebraicGeometry.mem_of_isSeparated_of_forall_smoothProperCurve_opens_mem`: let `Y` be integral, separated and locally
of finite type over an algebraically closed field `k`, and `S` a set of `k`-points of `Y` containing `y₀` and stable
along curves: whenever `ψ : U ⟶ Y` is a morphism from an open of a smooth proper integral curve over `k` and one
`k`-point of `U` maps into `S`, every `k`-point of `U` does. Then `S` contains every `k`-point of `Y`.

Proof. Section `Link` (`link`): two `k`-points in a common affine open `U = Spec B` are joined: by the ported
`Ideal.exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one` there is a prime `𝔭 ⊆` both maximal ideals with
`dim B/𝔭 = 1`, and the ported `exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one` gives a curve
through both points, so stability transfers membership. In general (`main`), choose affine opens `U₀ ∋ y₀`,
`U₁ ∋ y₁`; as `Y` is irreducible and Jacobson, `U₀ ∩ U₁` contains a closed point `w`, a `k`-point, and two applications of
`link` give `y₀ ~ w ~ y₁`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- abbrev `P2MW.S_AlgebraicGeometry_mem_of_isSeparated_of_forall_smoothProperCurve_opens_mem.P2mCurveConnectOpen.pt`
- theorem `P2MW.S_AlgebraicGeometry_mem_of_isSeparated_of_forall_smoothProperCurve_opens_mem.P2mCurveConnectOpen.isClosed_pt`
- def `P2MW.S_AlgebraicGeometry_mem_of_isSeparated_of_forall_smoothProperCurve_opens_mem.P2mCurveConnectOpen.CurveStable`
- def `P2MW.S_AlgebraicGeometry_mem_of_isSeparated_of_forall_smoothProperCurve_opens_mem.P2mCurveConnectOpen.algHomK`
- theorem `P2MW.S_AlgebraicGeometry_mem_of_isSeparated_of_forall_smoothProperCurve_opens_mem.P2mCurveConnectOpen.spec_map_algHomK`
- def `P2MW.S_AlgebraicGeometry_mem_of_isSeparated_of_forall_smoothProperCurve_opens_mem.P2mCurveConnectOpen.algK`
- theorem `P2MW.S_AlgebraicGeometry_mem_of_isSeparated_of_forall_smoothProperCurve_opens_mem.P2mCurveConnectOpen.finiteType_algK`
- theorem `P2MW.S_AlgebraicGeometry_mem_of_isSeparated_of_forall_smoothProperCurve_opens_mem.P2mCurveConnectOpen.link`
- theorem `P2MW.S_AlgebraicGeometry_mem_of_isSeparated_of_forall_smoothProperCurve_opens_mem.P2mCurveConnectOpen.main`
- theorem `P2MW.S_AlgebraicGeometry_mem_of_isSeparated_of_forall_smoothProperCurve_opens_mem.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one` (same contribution).
Other imports: `Mathlib`.
