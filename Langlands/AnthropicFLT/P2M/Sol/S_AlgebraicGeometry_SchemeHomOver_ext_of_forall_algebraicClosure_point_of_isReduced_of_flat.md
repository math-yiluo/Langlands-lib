# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Manual edit for Mathlib drift (FLT line 21, line 32 here): `⟨⊥, Ideal.bot_prime⟩` is replaced by `⟨⊥, Ideal.isPrime_bot⟩`. The constant `Ideal.bot_prime` no longer exists in the project's Mathlib; `Ideal.isPrime_bot` (Mathlib `RingTheory/Ideal/Prime.lean`) states the same fact, that `⊥` is a prime ideal of a nontrivial ring without zero divisors.
- Manual edit for Mathlib drift (FLT line 34, line 45 here): `⟨⊥, Ideal.bot_prime⟩` is replaced by `⟨⊥, Ideal.isPrime_bot⟩`. The constant `Ideal.bot_prime` no longer exists in the project's Mathlib; `Ideal.isPrime_bot` (Mathlib `RingTheory/Ideal/Prime.lean`) states the same fact, that `⊥` is a prime ideal of a nontrivial ring without zero divisors.
- Manual edit for Mathlib drift (FLT line 43, line 54 here): `⟨⊥, Ideal.bot_prime⟩` is replaced by `⟨⊥, Ideal.isPrime_bot⟩`. The constant `Ideal.bot_prime` no longer exists in the project's Mathlib; `Ideal.isPrime_bot` (Mathlib `RingTheory/Ideal/Prime.lean`) states the same fact, that `⊥` is a prime ideal of a nontrivial ring without zero divisors.
- Manual edit for Mathlib drift (FLT line 45, line 56 here): `⟨⊥, Ideal.bot_prime⟩` is replaced by `⟨⊥, Ideal.isPrime_bot⟩`. The constant `Ideal.bot_prime` no longer exists in the project's Mathlib; `Ideal.isPrime_bot` (Mathlib `RingTheory/Ideal/Prime.lean`) states the same fact, that `⊥` is a prime ideal of a nontrivial ring without zero divisors.
- Manual edit for Mathlib drift (FLT line 49, line 60 here): `⟨⊥, Ideal.bot_prime⟩` is replaced by `⟨⊥, Ideal.isPrime_bot⟩`. The constant `Ideal.bot_prime` no longer exists in the project's Mathlib; `Ideal.isPrime_bot` (Mathlib `RingTheory/Ideal/Prime.lean`) states the same fact, that `⊥` is a prime ideal of a nontrivial ring without zero divisors.
- Manual edit for Mathlib drift (FLT line 78, line 89 here): `⟨⊥, Ideal.bot_prime⟩` is replaced by `⟨⊥, Ideal.isPrime_bot⟩`. The constant `Ideal.bot_prime` no longer exists in the project's Mathlib; `Ideal.isPrime_bot` (Mathlib `RingTheory/Ideal/Prime.lean`) states the same fact, that `⊥` is a prime ideal of a nontrivial ring without zero divisors.
- Manual edit for Mathlib drift (FLT line 82, line 93 here): `⟨⊥, Ideal.bot_prime⟩` is replaced by `⟨⊥, Ideal.isPrime_bot⟩`. The constant `Ideal.bot_prime` no longer exists in the project's Mathlib; `Ideal.isPrime_bot` (Mathlib `RingTheory/Ideal/Prime.lean`) states the same fact, that `⊥` is a prime ideal of a nontrivial ring without zero divisors.
- Manual edit for Mathlib drift (FLT line 84, line 95 here): `⟨⊥, Ideal.bot_prime⟩` is replaced by `⟨⊥, Ideal.isPrime_bot⟩`. The constant `Ideal.bot_prime` no longer exists in the project's Mathlib; `Ideal.isPrime_bot` (Mathlib `RingTheory/Ideal/Prime.lean`) states the same fact, that `⊥` is a prime ideal of a nontrivial ring without zero divisors.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat`. Statement. `AlgebraicGeometry.SchemeHomOver.ext_of_forall_algebraicClosure_point_of_isReduced_of_flat`: let `R` be a
domain with fraction field `K` and algebraic closure `K̄`, `Y ⟶ Spec R` flat, locally of finite type and
reduced, and `X ⟶ Spec R` separated. Two morphisms `φ, ψ : Y ⟶ X` over `Spec R` that agree on all
`K̄`-points of `Y` (over `Spec R`) are equal.

Proof. The `K̄`-points of `Y` have dense image in `Y`: their image is the set of closed points of the
generic fibre (`range_specMap_eq`), which is dense in the generic fibre (Jacobson), and the generic fibre
is dense in `Y` by flatness over the domain `R` (`dense_preimage_genericPoint`, `dense_range_of_points`).
Two morphisms from a reduced scheme to a separated one that agree on a dense set of points (through
morphisms from spectra of fields) agree (`ext_of_forall_geometric_point`, the equalizer being a closed
subscheme containing a dense set).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat.RigKerGeomPoints.range_specMap_eq`
- theorem `P2MW.S_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat.RigKerGeomPoints.dense_preimage_genericPoint`
- theorem `P2MW.S_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat.RigKerGeomPoints.dense_range_of_points`
- theorem `P2MW.S_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat.RigKerGeomPoints.ext_of_forall_geometric_point`
- theorem `P2MW.S_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier` (Library).
Other imports: `Mathlib`.
