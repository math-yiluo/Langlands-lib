# The finite locus of a morphism

Internal infrastructure for the dense affine open step of task 22877948 (the conclusion of
`SeparatedDenseAffineOpenStatement`), following the finite-locus step in the proof of Stacks,
Properties of Spaces, Proposition 66.13.3 (Tag 06NH).

- `finiteLocus f` is the supremum of all opens `V` of the target with `f ∣_ V` finite.
  `le_finiteLocus` and `isFinite_restrict_of_le` hold, and `isFinite_restrict_finiteLocus`
  holds because finiteness is local on the target.
- `mem_minimalPrimes_of_mem_genericPoints`: generic points of `Spec A` are minimal primes.
- `genericPoints_subset_finiteLocus`: for `f` locally of finite type, locally quasi-finite,
  separated and quasi-compact to an affine scheme, every generic point of an irreducible
  component lies in the finite locus. The proof uses the generic finiteness theorem
  `GenericFiniteness.exists_not_mem_isFinite_morphismRestrict_basicOpen_of_mem_minimalPrimes`,
  adapted from the Anthropic FLT source in `Morphisms/GenericFiniteness`.
