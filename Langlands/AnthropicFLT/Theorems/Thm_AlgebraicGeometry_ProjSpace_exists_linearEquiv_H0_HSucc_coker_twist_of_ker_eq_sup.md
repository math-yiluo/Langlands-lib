# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.solution n k Zk ιk ℓ hℓ hnzd 𝓘ℓ h𝓘ℓ Z' ι' hker d htc μ hμ`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 21 here); in 3 lines the replacements `Type` (universe 0) → `Type uz` (1 place), `Scheme.{0}` → `Scheme.{uz}` (2 places) are made, and these lines are otherwise unchanged. Consequently the theorem statement becomes universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.ProjSpace.exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup`: in the hyperplane
situation (a closed immersion `ιk : Z_k ⟶ ℙⁿ_k`, a linear form `ℓ` acting injectively on the charts,
the hyperplane section `ι' : Z' ⟶ ℙⁿ_k` with ideal `ker ιk ⊔ (ℓ)`, and the multiplication by `ℓ` map
`μ : 𝒪_{Z_k}(d) → 𝒪_{Z_k}(d + 1)`), the Čech cohomology groups of `coker μ` are isomorphic to those of
`𝒪_{Z'}(d + 1)`, compatibly with the classes given by forms of degree `d + 1`.

The proof term applies the companion solution theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.solution`.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above.

- theorem `AlgebraicGeometry.ProjSpace.exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCover` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions` (Library), `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup` (same contribution).
Other imports: `Mathlib`.
