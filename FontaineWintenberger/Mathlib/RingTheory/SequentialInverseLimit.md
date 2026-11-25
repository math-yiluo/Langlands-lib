# Sequential inverse limits of commutative rings

Module `FontaineWintenberger.Mathlib.RingTheory.SequentialInverseLimit`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Given commutative rings `B n` indexed by `ℕ` (all in one universe) and ring homomorphisms `q n : B (n + 1) →+* B n`, the file builds the inverse limit as a subring of the product `∀ n, B n` and records its algebraic and topological properties. Everything lives in the namespace `FontaineWintenberger.SequentialInverseLimit`.

## Definitions

- `subring B q`: the subring of compatible families, defined as the intersection over `n` of the equalizers of `(q n).comp (Pi.evalRingHom B (n + 1))` and `Pi.evalRingHom B n`. `mem_subring` unfolds this: `a` is a member iff `q n (a (n + 1)) = a n` for all `n`.
- `projection B q n : subring B q →+* B n`: evaluation at the `n`-th coordinate.
- `transition B q i j hij : B j →+* B i` for `i ≤ j`: the composite of the adjacent maps `q`, defined by recursion on `j`.

## Results

- `compatible`, `transition_projection`: the projections commute with the adjacent maps and with all composite transitions. `transition_self`, `transition_succ`, `transition_succ_self`, `transition_succ_left` are the calculation rules for `transition`.
- `projection_surjective`: if every `q n` is surjective, every projection is surjective. No finiteness of the rings is assumed. The proof extends a given element of `B n` downward by the transitions and upward by chosen preimages (a private recursive construction using `Function.surjInv`).

With each `B n` carrying a uniform structure that is discrete (`DiscreteUniformity`), and the subring carrying the uniformity induced from the product:

- `isClosed_subring`: the subring is closed in the product.
- `completeSpace`, `t2Space`: the subring is complete and Hausdorff.
- `nhds_zero_hasBasis_ker_projection`: the kernels of the projections `projection B q n`, `n ∈ ℕ`, form a basis of neighbourhoods of `0`. Compatibility reduces a condition on finitely many coordinates to the condition at the largest index.

`continuous_projection` and `uniformContinuous_projection` hold for arbitrary uniform structures on the `B n`; discreteness is not used there.

## What to watch for

- The limit is a `Subring` of the product, not a categorical limit object of Mathlib; no universal property is stated in this file.
- `completeSpace` and `t2Space` are stated as theorems, not registered as instances.
- The topological statements about closedness, completeness and the neighbourhood basis require the discrete uniformity on every `B n`.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Mathlib/RingTheory/SequentialInverseLimit.lean` (SHA-256 of the source file `64c816f6cd40f0e6f4d051365902f8ca0957a921c2679abbdbf5893d38f2ce65`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
