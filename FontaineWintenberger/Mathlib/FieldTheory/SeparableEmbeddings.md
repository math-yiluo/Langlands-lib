# Extending embeddings in normal and separably closed fields

Module `FontaineWintenberger.Mathlib.FieldTheory.SeparableEmbeddings`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

The file collects three statements on extending embeddings, each a direct application of a lifting result of Mathlib.

## Main results

- `exists_aut_extends_intermediate_embedding`: let `Ω/K` be a normal extension, `S` an intermediate field and `i : S → Ω` a `K`-embedding. Then some `K`-automorphism `σ` of `Ω` satisfies `σ x = i x` for all `x ∈ S`.
- `exists_aut_extends_separableClosure_embedding`: the same statement for `Ω = SeparableClosure K`.
- `nonempty_separablyClosed_embeddings`: if `L/K` is a separable algebraic extension and `Ω` is a separably closed field that is a `K`-algebra, there is a `K`-embedding `L → Ω`.

## Proofs

The first uses `AlgHom.liftNormal`, whose result is bijective because `Ω/K` is normal. The third is `IsSepClosed.lift`.

## Points to watch

- The automorphism in the first two statements is not unique, and is obtained by a choice.
- In the third statement `Ω` is not assumed algebraic over `K`.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Mathlib/FieldTheory/SeparableEmbeddings.lean` (SHA-256 of the source file `08a257629cef193639ba335c99a0fc92d5628f84f90e7d67128b86aefcfc64d3`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
