# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_polynomial_natDegree_le_forall_eulerChar_twist_stdCoverPullback_eq`

Ported for the proof of projective representability of the relative endomorphism functor of a projective abelian scheme, `Langlands.AbelianScheme.relativeEndomorphismRepresentability`, which depends on this module through its imports. Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_polynomial_natDegree_le_forall_eulerChar_twist_stdCoverPullback_eq.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`.

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; `import Mathlib` is now `import Langlands.MathlibBase` (all of Mathlib except the three modules that clash with weil-conjectures, see `Langlands/MathlibBase.md`).
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 2 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept.
- No other change: apart from the renames described under “Names changed by the Library” below, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_polynomial_natDegree_le_forall_eulerChar_twist_stdCoverPullback_eq.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_polynomial_natDegree_le_forall_eulerChar_twist_stdCoverPullback_eq`. Statement. `AlgebraicGeometry.ProjSpace.exists_polynomial_natDegree_le_forall_eulerChar_twist_stdCoverPullback_eq`:
for a closed subscheme `ι : Z ⟶ ℙⁿ_k` over a field, the Euler characteristic of the twist `𝒪_Z(d)` (for
the pulled-back standard cover) is a polynomial in `d` of degree `≤ n`.

Proof. `NatFamily`, `cochainMap`, `eulerChar_eq_of_natFamily`: bijective compatible families of maps on
the intersections of the cover preserve Euler characteristics. The ported
`ProjSpace.exists_projPresentation_toProj_eq_and_locallyTrivial` gives an invertible module `L = 𝒪_Z(1)`
with a presentation by `ι`; the ported
`Scheme.Modules.ProjPresentation.exists_linearMap_sections_tensorPow_twistObj_monoidalV2` identifies
`L^{⊗d}` with the twist on the cover members, so the Euler characteristics agree (also using
`OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso` and
`LinearMap.nonempty_kerModRange_equiv_of_equiv_comm`). The structure sheaf of `Z` is coherent and
quasi-coherent (`OModulePresheaf.isCoherent_ofModules_of_locallyTrivial`, `…isQuasicoherent…`) and
supported in `Z`, of dimension `≤ n` (`ProjSpace.topologicalKrullDim_le_of_isClosedImmersion`), so
Snapper's theorem `OModulePresheaf.exists_polynomial_forall_eulerChar_tensor_tensorPow_eq_monoidalV2`
gives the polynomial.

## Declarations

Names, namespaces and statements are the FLT ones, apart from the renames described under “Names changed by the Library” below. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- structure `P2MW.S_AlgebraicGeometry_ProjSpace_exists_polynomial_natDegree_le_forall_eulerChar_twist_stdCoverPullback_eq.C5bSol.NatFamily`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_polynomial_natDegree_le_forall_eulerChar_twist_stdCoverPullback_eq.C5bSol.appₗ`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_polynomial_natDegree_le_forall_eulerChar_twist_stdCoverPullback_eq.C5bSol.appₗ_apply`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_polynomial_natDegree_le_forall_eulerChar_twist_stdCoverPullback_eq.C5bSol.cochainMap`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_polynomial_natDegree_le_forall_eulerChar_twist_stdCoverPullback_eq.C5bSol.cochainMap_apply`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_polynomial_natDegree_le_forall_eulerChar_twist_stdCoverPullback_eq.C5bSol.cochainMap_d`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_polynomial_natDegree_le_forall_eulerChar_twist_stdCoverPullback_eq.C5bSol.cochainMap_bijective`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_polynomial_natDegree_le_forall_eulerChar_twist_stdCoverPullback_eq.C5bSol.eulerChar_eq_of_natFamily`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_polynomial_natDegree_le_forall_eulerChar_twist_stdCoverPullback_eq.C5bSol.eulerChar_eq_of_nonempty_equiv`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_polynomial_natDegree_le_forall_eulerChar_twist_stdCoverPullback_eq.C5bSol.supportedIn_top`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_polynomial_natDegree_le_forall_eulerChar_twist_stdCoverPullback_eq.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCover` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum` (ported together with this module), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar` (ported together with this module), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation` (ported together with this module), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_tensor_tensorPow_eq_monoidalV2` (ported together with this module), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_linearMap_sections_tensorPow_twistObj_monoidalV2` (ported together with this module), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso` (ported together with this module), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_ofModules_of_locallyTrivial` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial` (Library), `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_nonempty_kerModRange_equiv_of_equiv_comm` (ported together with this module), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_projPresentation_toProj_eq_and_locallyTrivial` (ported together with this module), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_topologicalKrullDim_le_of_isClosedImmersion` (ported together with this module).
Other imports: `Langlands.MathlibBase`.

## Names changed by the Library (22 November 2026)

weil-conjectures, on which the Library depends, declares 21 of the names of this extract itself, so that no module could import both. The Library renamed these 21 declarations: each keeps its name space and the last component of its name gets the marker `FLT` (`tensorPow` becomes `tensorPowFLT`, `tensorPow_zero` becomes `tensorPowFLT_zero`). In this file:

- its uses of `AlgebraicGeometry.Scheme.Modules.tensorPow` are uses of `tensorPowFLT` now.

Statements and proofs are otherwise unchanged. Elsewhere on this page the names are given as they now are.
