# Krasner's lemma: descent and uniqueness of the nearby conjugate

Module `FontaineWintenberger.Mathlib.Analysis.Krasner`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Mathlib's Krasner lemma over a complete base, with uniqueness of the nearby embedding.

## Main results

Let `K` be a complete ultrametric nontrivially normed field and `Ω` a normed field that is a separable normal normed `K`-algebra.

- `krasner_mem_adjoin`: if `‖a − b‖ < ‖a − a′‖` for every conjugate `a′ ≠ a` of `a` over `K`, then `a ∈ K⟮b⟯`.
- `krasner_mem_adjoin_and_unique`: if `δ ≤ ‖a − c‖` for every conjugate `c ≠ a`, and `‖a − b‖ < δ`, then `a ∈ K⟮b⟯`, and the inclusion is the only `K`-embedding `f : K⟮a⟯ → Ω` with `‖f(a) − b‖ < δ`.

For any field `K` and ultrametric normed field `Ω` that is a `K`-algebra:

- `isConjRoot_adjoin_simple_gen_image`: a `K`-embedding `K⟮a⟯ → Ω` sends `a` to a conjugate of `a`.
- `conjugate_eq_of_norm_sub_lt`: under the separation hypothesis, a conjugate `a′` with `‖a′ − b‖ < δ` and `‖a − b‖ < δ` equals `a`.
- `nearby_simple_embedding_unique`: the uniqueness statement alone.

Conjugates are taken inside `Ω`.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Mathlib/Analysis/Krasner.lean` (SHA-256 of the source file `7e6685b24ac33080e35a07a4518e8654f9640d7fcbe577f251ba23d777a4e0e1`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
