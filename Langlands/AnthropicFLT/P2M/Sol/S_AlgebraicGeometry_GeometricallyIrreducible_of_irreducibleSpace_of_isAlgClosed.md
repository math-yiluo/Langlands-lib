# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

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

The theorem `P2MW.S_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed`. Statement. `AlgebraicGeometry.GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed`: over an
algebraically closed field `k`, a morphism `f : X ⟶ Spec k` from an irreducible scheme is geometrically
irreducible.

Proof (namespace `IsAlgClosed.BaseChangeIrreducible`). Section `FiniteType`: for a domain `A` of
finite type over the algebraically closed `K`, residue fields at maximal ideals are `K`
(`algebraMap_quotient_bijective`, giving `K`-points `pointOfMaximal`), and `A ⊗[K] B` is a domain for
every domain `B` (`isDomain_tensorProduct_of_finiteType`: a zero divisor would vanish at all
`K`-points of `A`). Section `Fields`: the same for a field `F` over `k` in place of `A`
(`isDomain_tensorProduct_of_field`, by passing to finitely generated subalgebras). Section
`Schemes`: for a field extension `K / k`, the fibres of `X_K ⟶ X` are irreducible
(`irreducibleSpace_fiber_fst`), and `X_K` is irreducible (`irreducibleSpace_pullback`). By
`geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms` this is geometric irreducibility.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed.IsAlgClosed.BaseChangeIrreducible.algebraMap_quotient_bijective`
- def `P2MW.S_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed.IsAlgClosed.BaseChangeIrreducible.pointOfMaximal`
- theorem `P2MW.S_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed.IsAlgClosed.BaseChangeIrreducible.pointOfMaximal_eq_zero_iff`
- theorem `P2MW.S_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed.IsAlgClosed.BaseChangeIrreducible.isDomain_tensorProduct_of_finiteType`
- theorem `P2MW.S_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed.IsAlgClosed.BaseChangeIrreducible.isDomain_tensorProduct_of_field`
- theorem `P2MW.S_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed.IsAlgClosed.BaseChangeIrreducible.irreducibleSpace_fiber_fst`
- theorem `P2MW.S_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed.IsAlgClosed.BaseChangeIrreducible.irreducibleSpace_pullback`
- theorem `P2MW.S_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib.AlgebraicGeometry.Geometrically.Irreducible`, `Mathlib.AlgebraicGeometry.Fiber`, `Mathlib.FieldTheory.IsAlgClosed.Basic`, `Mathlib.RingTheory.Jacobson.Ring`, `Mathlib.RingTheory.TensorProduct.Nontrivial`, `Mathlib.RingTheory.TensorProduct.Free`, `Mathlib.RingTheory.Flat.Basic`, `Mathlib.LinearAlgebra.TensorProduct.Finiteness`.
