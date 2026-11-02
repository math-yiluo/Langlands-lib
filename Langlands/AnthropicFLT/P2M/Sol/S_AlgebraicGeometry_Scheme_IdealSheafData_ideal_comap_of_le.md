# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 4 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept.
- 6 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le`. Statement. `AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_le`: for an ideal sheaf `I` on `X`, `f : Y ⟶ X`
and affine opens `U ⊆ X`, `V ⊆ Y` with `V ⊆ f⁻¹ U`, the ideal of the pullback `I.comap f` on `V` is the
extension of the ideal of `I` on `U` along `Γ(X, U) → Γ(Y, V)`.

Proof. The pullback ideal sheaf is the kernel of the pulled-back closed immersion; for affine opens it is
computed by the base change of rings: the kernel of `Γ(Y, V) → Γ(Y, V) ⊗_{Γ(X,U)} Γ(X,U)/I(U)` is the
extended ideal (`ker_algebraMap_eq_map_ker`, `ker_eq_map_ker_of_isPushout`, using the pushout of affine
schemes). The cases of `⊤` and of affine morphisms (`ideal_comap_top`, `ideal_comap_of_isAffineHom`) are
reduced to this.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le.Algebra.IsPushout.ker_algebraMap_eq_map_ker`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le.CommRingCat.ker_eq_map_ker_of_isPushout`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le.AlgebraicGeometry.Scheme.IdealSheafData.ComapLocal.ideal_comap_top`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le.AlgebraicGeometry.Scheme.IdealSheafData.ComapLocal.ideal_comap_of_le`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le.AlgebraicGeometry.Scheme.IdealSheafData.ComapLocal.ideal_comap_of_isAffineHom`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`, `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`, `Mathlib.RingTheory.RingHom.Flat`, `Mathlib.RingTheory.LocalProperties.Basic`, `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`, `Mathlib.Algebra.Category.Ring.Constructions`, `Mathlib.LinearAlgebra.TensorProduct.RightExactness`, `Mathlib.RingTheory.IsTensorProduct`.
