# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral`

Ported module of the proof submitted by task `e36ae7da-512e-4a4d-a902-71146c92ec82` (descent of properness to finitely generated subalgebras). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 14 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Proof (namespace `SolCHint`; the classical construction of Chow's lemma). Charts (`exists_chart`, `ChartData`): cover `X` by finitely many
nonempty affine opens `Uₖ`; each `Γ(Uₖ)` is a quotient of a polynomial ring over `A` in `eₖ` variables, so
the ratio theorem `ProjSpace.exists_algHom_away_apply_ratio_eq` gives a closed immersion `cₖ` of `Uₖ` into
the standard chart `D₊(X₀)` of `ℙ^{eₖ}_A`, hence an immersion `ιₖ : Uₖ → ℙ^{eₖ}_A` over `A`. Let
`U₀ = ⋂ Uₖ` (nonempty, `X` integral), `Π = ∏ₖ ℙ^{eₖ}_A` over `Spec A` (`ProjSpace.prodOver`, proper), and let
`X'` be the scheme-theoretic image of the immersion `ψ = (incl, (ιₖ)ₖ) : U₀ → X ×_A Π`; `π` and `ιι` are
the two projections restricted to `X'`. Then `X'` is integral, `π` is proper, and `ψ` identifies `U₀` with
a dense open of `X'`. Step 1 (`ak_eq_bk`): over `Vₖ = π⁻¹(Uₖ)` the two maps `Vₖ → ℙ^{eₖ}` (through `ιₖ`
and through `Π`) agree, since they agree on the dense open `U₀` and the target is separated
(`ext_of_isDominant_of_isSeparated`); so `ιι` maps `Vₖ` into `Ωₖ = prₖ⁻¹ D₊(X₀)`. Step 3
(`isClosedImmersion_ιΩ`): `Vₖ → Ωₖ` is a closed immersion, as a base change of the closed immersion `cₖ`
composed with a closed immersion into a fibre product. Step 2 (`V_eq_O`): `Vₖ = ιι⁻¹(Ωₖ)`: the open immersion
`Vₖ → ιι⁻¹(Ωₖ)` is proper (its composite with the separated `ιι` is the closed immersion of Step 3), so its
image is nonempty, open and closed in the irreducible open `ιι⁻¹(Ωₖ)` of `X'`. Step 4: hence the restriction of `ιι`
over each `Ωₖ` is a closed immersion, so `ιι` is a closed immersion into the open `⋃ₖ Ωₖ` of `Π`
(`isClosedImmersion_ιall`, local on the target), so an immersion, and `π` is
surjective since its image is closed and contains the dense set `U₀` (`surjective_π`). Finally (`chow`)
`P` is the scheme-theoretic image of `ιι` in `Π`, `j` the induced open immersion `X' → P`, and `q` the
proper map `P → Π → Spec A`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- abbrev `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.grading`
- abbrev `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.PP`
- abbrev `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.W`
- abbrev `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.awayι₀`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ι_comp_eq_isoSpec_hom`
- theorem `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.exists_chart`
- structure `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData`
- theorem `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.nonempty_chartData`
- def `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.ι`
- scoped unnamed instance `instance (k : Fin D.m) : IsImmersion (D.ι k)`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.ι_comp_π`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.range_ι_subset`
- abbrev `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.PiS`
- abbrev `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.prπ`
- abbrev `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.pr`
- def `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.Ω`
- def `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.Uo`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.Uo_le`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.mem_Uo`
- def `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.g`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.g_comp_prπ`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.g_comp_pr`
- abbrev `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.XP`
- def `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.ψ`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.ψ_fst`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.ψ_snd`
- scoped unnamed instance `instance : IsImmersion D.ψ`
- abbrev `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.X'`
- abbrev `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.α`
- abbrev `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.ψ'`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.ψ'_α`
- def `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.π`
- def `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.ιι`
- scoped unnamed instance `instance : IsProper D.π`
- scoped unnamed instance `instance [IsSeparated f] : IsSeparated D.ιι`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.π_comp_f`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.ψ'_π`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.ψ'_ιι`
- def `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.V`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.isNoetherian_X`
- scoped instance `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.noetherianSpace_Uo`
- scoped instance `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.compactSpace_XP`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.Uo_nonempty`
- scoped instance `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.nonempty_Uo`
- scoped instance `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.isIntegral_Uo`
- scoped instance `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.quasiCompact_ψ`
- scoped unnamed instance `instance : IsOpenImmersion D.ψ'`
- scoped unnamed instance `instance : IsDominant D.ψ'`
- scoped instance `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.isReduced_X'`
- scoped instance `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.irreducibleSpace_X'`
- scoped instance `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.isIntegral_X'`
- scoped instance `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.compactSpace_X'`
- def `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.πk`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.πk_ι`
- def `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.ak`
- def `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.bk`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.range_ψ'_subset_V`
- def `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.ψk`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.ψk_ι`
- scoped unnamed instance `instance (k : Fin D.m) : IsDominant (D.ψk k)`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.ψk_πk`
- theorem `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.ak_eq_bk`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.pr_ιι_apply`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.V_le_preimage_Ω`
- def `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.ιΩ`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.ιΩ_ι`
- abbrev `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.T`
- def `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.mT`
- scoped unnamed instance `instance (k : Fin D.m) : IsOpenImmersion (D.mT k)`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.mT_fst`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.mT_snd`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.range_mT`
- def `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.tk`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.tk_mT`
- scoped unnamed instance `instance (k : Fin D.m) : IsClosedImmersion (D.tk k)`
- def `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.rk`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.rk_awayι`
- abbrev `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.G`
- def `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.tk'`
- abbrev `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.ik`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.c_ik`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.rk_ik`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.tk'_comp`
- scoped unnamed instance `instance (k : Fin D.m) : IsClosedImmersion (D.tk' k)`
- theorem `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.isClosedImmersion_ιΩ`
- abbrev `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.O`
- abbrev `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.ek`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.ek_comp`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.V_nonempty`
- scoped instance `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.nonempty_O`
- scoped instance `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.isProper_ek`
- theorem `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.V_eq_O`
- scoped instance `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.isClosedImmersion_restrict`
- def `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.Ωall`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.range_ιι_subset`
- def `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.ιall`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.ιall_ι`
- scoped instance `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.isClosedImmersion_ιall`
- scoped instance `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.isImmersion_ιι`
- scoped instance `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.isNoetherian_X'`
- scoped instance `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.quasiCompact_ιι`
- scoped instance `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.surjective_π`
- theorem `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData.chow`
- theorem `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.main`
- theorem `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (published with the FLT port of task `69435287-9f1e-4abd-8483-5e65ff23668a`), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq` (ported by this task).
All modules also import `Mathlib`.
