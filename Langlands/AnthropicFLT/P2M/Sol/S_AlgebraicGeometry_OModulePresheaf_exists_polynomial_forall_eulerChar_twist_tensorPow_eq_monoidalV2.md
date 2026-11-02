# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept.
- 1 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2`. Statement. `AlgebraicGeometry.OModulePresheaf.exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2`
(Snapper's theorem, Čech form): for `π : V ⟶ Spec k` proper over a field, an ordered affine cover `K`,
a coherent quasi-coherent FLT presheaf `G` supported in a closed set `Y` of topological Krull dimension
`≤ d`, and a locally trivial module `L`, the function `n ↦ χ(G ⊗ L^{⊗n})` is a polynomial of degree
`≤ d`.

Proof (namespace `P2mChiDatum`). Difference calculus: a function on `ℕ` whose first differences are a
polynomial of degree `< e` is a polynomial of degree `< e + 1` (`ext`, `fwdDiff_ext`, `poly_of_delta`).
Section `Dim`: integral closed subschemes have irreducible support, proper closed subsets of an
irreducible closed set have smaller dimension (`dim_lt_of_lt`), monotonicity and nonnegativity of
dimension. Section `Skeleton` (`chi`, `Good`, `P e G`: `χ(G ⊗ L^n)` is a polynomial of degree `< e`):
noetherian induction on the support (`skeleton`), given a dévissage principle `hDev` and the twisting
step `hTwist`. Section `Inputs`: additivity of `χ` on short exact sequences after twisting (`chi_add`,
from the ported tensor-exactness and Euler-characteristic additivity), vanishing for zero presheaves,
the class `Q Y G` (polynomiality in all admissible degrees) closed under extensions (`Q_ext`); `hDev`
from the ported dévissage `OModulePresheaf.forall_of_forall_integral`, and `hTwist` from
`OModulePresheaf.exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2`. `card` assembles the
result with degree `≤ d`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- private def `P2mChiDatum.ext`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2.P2mChiDatum.ext_natCast`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2.P2mChiDatum.ext_neg_succ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2.P2mChiDatum.fwdDiff_ext`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2.P2mChiDatum.poly_of_delta`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2.P2mChiDatum.isIrreducible_of_isIntegral_subscheme`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2.P2mChiDatum.dim_lt_of_lt`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2.P2mChiDatum.dim_mono`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2.P2mChiDatum.dim_nonneg`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2.P2mChiDatum.chi`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2.P2mChiDatum.Good`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2.P2mChiDatum.P`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2.P2mChiDatum.IH`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2.P2mChiDatum.OZ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2.P2mChiDatum.skeleton`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2.P2mChiDatum.locTriv_tensorPow`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2.P2mChiDatum.good_twist`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2.P2mChiDatum.cechFinite_twist`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2.P2mChiDatum.flat_sections`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2.P2mChiDatum.chi_add`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2.P2mChiDatum.eulerChar_eq_zero_of_subsingleton`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2.P2mChiDatum.chi_eq_zero_of_subsingleton`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2.P2mChiDatum.Q`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2.P2mChiDatum.Q_zero`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2.P2mChiDatum.Q_mono`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2.P2mChiDatum.Q_ext`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2.P2mChiDatum.hDev`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2.P2mChiDatum.hTwist`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2.P2mChiDatum.card`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafTensor` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor` (Library), `Langlands.AnthropicFLT.Theorems.Thm_fwdDiff_iter_succ_eq_zero_iff_exists_polynomial_natDegree_le` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_affSES_tensor_of_flat` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_forall_coherent_of_forall_integral` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_isCoherent_supportedIn_tensor` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_ofModules_of_locallyTrivial` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_projective_sections_of_locallyTrivial` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2` (Library).
Other imports: `Mathlib`.
