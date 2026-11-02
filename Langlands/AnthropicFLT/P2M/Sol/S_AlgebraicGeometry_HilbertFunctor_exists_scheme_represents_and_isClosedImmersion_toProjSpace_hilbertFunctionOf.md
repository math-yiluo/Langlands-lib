# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_hilbertFunctionOf`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_hilbertFunctionOf.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 19 here); in 7 lines the replacements `Type` (universe 0) → `Type uz` (6 places), `Scheme.{0}` → `Scheme.{uz}` (1 place) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; the further changes are listed in the next item.
- Further changes (universe generalization): The FLT construction works over the absolute base `Spec ℤ`. With schemes in universe `uz`, the ring `ℤ : Type` can only serve as a base in universe 0, so the absolute base ring `ℤ` is replaced by `ULift.{uz} ℤ` (the ring `ℤ` lifted to universe `uz`, isomorphic to `ℤ`). The new helper module `Langlands.AlgebraicGeometry.ULiftIntAlgebra` provides the `ULift ℤ`-algebra structure of every commutative ring (`Langlands.ULiftInt.algebra`), algebra maps from ring maps (`Langlands.ULiftInt.toAlgHom`), uniqueness of ring maps out of `ULift ℤ` (`Langlands.ULiftInt.ringHom_ext`) and noetherianity of `ULift ℤ`. In this file this module is imported. In the statement, the projective space `Proj ℤ[X₀, …, X_N]` receiving the closed immersion becomes `Proj (ULift ℤ)[X₀, …, X_N]`; otherwise the statement only changes by the universe generalization. The proof is the FLT proof with these replacements. The changed lines are:
  - after line 10 here, inserted:
    replacement:

    ```lean
    import Langlands.AlgebraicGeometry.ULiftIntAlgebra
    ```
  - line 46 here:
    FLT text (universe-0 port):

    ```lean
            ∃ (N : ℕ) (ι : Hilb ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℤ)),
    ```

    replacement:

    ```lean
            ∃ (N : ℕ) (ι : Hilb ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (ULift.{uz} ℤ))),
    ```
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_hilbertFunctionOf.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_hilbertFunctionOf`. Statement. `AlgebraicGeometry.HilbertFunctor.exists_scheme_represents_and_isClosedImmersion_toProjSpace_hilbertFunctionOf`:
for a Hilbert polynomial `P` there is `D₀` such that for every `m ≥ D₀`: points with Hilbert function
`hilbertFunctionOf n P m` are stable under base change, and there are a scheme `Hilb` (universe `uz`)
and bijections `pt A` between such points over `A` and morphisms `Spec A ⟶ Hilb`, natural in ring maps
`A → B` (when the ideal of the second point is the extension of the first), together with a closed
immersion of `Hilb` into a projective space `ℙᴺ` over `ULift ℤ` (the integers in universe `uz`;
FLT: over `ℤ`).

Proof. Take `D₀` from the ported
`MvPolynomial.exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval` (Macaulay/Gotzmann bounds
for `P`). For `m ≥ D₀`, the function `h = hilbertFunctionOf n P m` equals `C(n + d, n)` below `m`,
satisfies the persistence bound and is attained in consecutive degrees beyond `m`, so the ported
`HilbertFunctor.exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth` applies.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_hilbertFunctionOf.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval` (same contribution).
Other project modules imported: `Langlands.AlgebraicGeometry.ULiftIntAlgebra` (same contribution).
Other imports: `Mathlib`.
