# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 3 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 19 here); in 4 lines the replacements `Type` (universe 0) → `Type uz` (2 places), `Scheme.{0}` → `Scheme.{uz}` (3 places) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup`. Statement. `AlgebraicGeometry.ProjSpace.exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup`: in the hyperplane
situation (a closed immersion `ιk : Z_k ⟶ ℙⁿ_k`, a linear form `ℓ` acting injectively on the charts,
the hyperplane section `ι' : Z' ⟶ ℙⁿ_k` with ideal `ker ιk ⊔ (ℓ)`, and the multiplication by `ℓ` map
`μ : 𝒪_{Z_k}(d) → 𝒪_{Z_k}(d + 1)`), the Čech cohomology groups of `coker μ` are isomorphic to those of
`𝒪_{Z'}(d + 1)`, compatibly with the classes given by forms of degree `d + 1`.

Proof (namespace `P2mQuotSec`). Section `Generic`: kernels and quotients of compatible maps of complexes
(`kerEquiv`, `HQ`, `HQEquiv`). Sections `Transport`, `Res`, `Principal`: restriction between equal
opens, dehomogenization of multiples of `ℓ`. Section `Main`: the restriction of twist sections from
`Z_k` to `Z'` (`resJ`, defined chart-wise via `resJVal`, compatible with restrictions and scalars) is
surjective on affine pieces with kernel the image of `μ` (`resJ_surjective`, `resJ_eq_zero_iff`, using
the description of the ideal of `Z'` on the charts, `ideal_𝓘ℓ_eq`, `ker_app_eq_span`, and the cocycle
`tℓ` of `ℓ`). Section `Cech`: on the intersections of the cover this identifies `coker μ` with the twist
of `Z'` (`T`, `Φ` bijective and commuting with the differentials, `Φ_comm`), giving the isomorphisms
`e₀` and `eS` of `H⁰` and `Hⁱ⁺¹`, with the compatibility for forms (`e₀_proj_val`).

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.kerEquiv`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.kerEquiv_apply_val`
- abbrev `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.HQ`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.HQEquiv`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.HQEquiv_mk`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.res_irrel`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.res_eq_bijective`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.preimage_iInf_fin`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.restrictFun_bijective_of_le_le`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.restrictFun_injective_of_le_le`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.app_restrictFun`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.X_pow_mem`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.frac`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.frac_mul`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.frac_eq_zero`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.frac_congr`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.frac_mem_span`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.pullbackChart_comp`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.frameUnit_comp`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.resJVal`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.resJVal_compat`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.app_algebraMap`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.resJ`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.resJ_val`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.resJ_res`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.resJ_smul`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.spread_compat`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.spread`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.spread_val`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.eq_spread`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.twist_zero_val`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.tℓ`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.ideal_𝓘ℓ_eq`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.ker_app_eq_span`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.app_tℓ_eq_zero`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.resJ_surjective`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.resJ_eq_zero_iff`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.resJ_surjective'`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.resJ_eq_zero_iff'`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.restrictFun_app_awayToSection_left`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.restrictFun_app_awayToSection_right`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.awayMap_tfrac`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.tℓ_cocycle`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.K'_inter`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.K_inter`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.σ`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.σ_mk`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.σ_res`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.T`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.T_res`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.T_bijective`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.Φ`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.Φ_apply`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.Φ_bijective`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.Φ_comm`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.e₀`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.eS`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.e₀_val`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.P2mQuotSec.e₀_proj_val`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCover` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions` (Library).
Other imports: `Mathlib`.
