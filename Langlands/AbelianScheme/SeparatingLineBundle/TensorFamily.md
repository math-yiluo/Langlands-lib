# Finite tensor products of line-bundle sections

Helper module for the proof of
`Langlands.GroupScheme.AlgebraicallyClosedSeparatingLineBundleStatement`
(task `eda1f6ff-d036-4f23-aabb-7663e7606b42`). It imports the published proof module
`Langlands.AlgebraicGeometry.Picard.LineBundleSectionVanishingProof`. From that module
and the transport proof it imports, it uses the
two-factor lemmas `vanishesAlong_field_iff`, `vanishesAlong_tensor_right_iff`,
`vanishesAlong_tensor_left_iff` and `trivializationOpen_one`.

`W(s)` is the trivialization open `trivializationOpen L.obj s`. `VanishesAlong L f s`
means that `pullbackSection f L.obj s` is zero.

## Definitions

- `tensorLB L M`: the line bundle `LineBundle.tensor pullbackTensorComparisonIsIso L M`,
  whose underlying module is `tensorObj L.obj M.obj`. It is an abbreviation, so the
  published two-factor lemmas apply to it directly.
- `famBundle n N`: the tensor product of `N 0, …, N (n-1)`, defined by recursion on `n`
  with `Fin.tail`. The empty product is the trivial line bundle.
- `famSection n N σ`: the corresponding product of sections. The empty product is the
  unit section `1`.

## Results

- `mem_trivializationOpen_famSection_iff`: `x ∈ W(∏ σ i)` exactly when `x ∈ W(σ i)` for
  every `i`. The proof is induction on `n`, using `W(1) = ⊤` and the Library identity
  `W(s ⊗ u) = W(s) ⊓ W(u)` (`tensorSectionGenerationLocus`).
- `vanishesAlong_famSection_field_iff`: at a point `x : Spec K ⟶ X` with `K` a field,
  the product section vanishes exactly when some factor does. Both sides reduce to
  membership in trivialization opens by `vanishesAlong_field_iff`.
- `vanishesAlong_famSection_iff_of_mem n N σ f j h`: suppose every factor `i ≠ j` satisfies
  `f y ∈ W(σ i)` for every point `y`. Then the product vanishes along `f` exactly when
  the `j`-th factor does. The proof is induction on `n`. When `j` is a successor, it
  cancels the head factor with `vanishesAlong_tensor_left_iff`. When `j = 0`, it cancels
  the tail product with `vanishesAlong_tensor_right_iff` instead.


## Provenance and authorship

This is internal derived content, proved by recursion from the published two-factor
section lemmas. Its constructions and complete proofs were recovered from the shared
draft by Worker 899 of the previous instance. Worker 2441 checked the recovered code in the
current environment and updated its documentation. The module is supporting work for
the separating-bundle assembly and does not itself prove that target.
