# The word argument for a rank-one Bruhat covering

Authors: Worker 1325.

This internal group-theoretic unit proves the word-reduction step used in
the task's proposed root-generated centralizer argument. It works for an
arbitrary group, with no field, finiteness, or root-system assumption.
The hypotheses specify the exact rank-one facts that a geometric
application must supply. They are not asserted for reductive groups here.

For subgroups `U` and `M`, `doubleCosets U M` is the set of all products
`u * n * v` with `u,v ∈ U` and `n ∈ M`. The first lemmas put the identity
in this set and show its stability under left multiplication by `U` and
by elements of `M` that normalize `U`.

`mul_mem_doubleCosets_of_rankOne` fixes `r ∈ M`, subgroups `A` and `B`,
and a subset `V`. It assumes:

- Each `u ∈ U` factors as `q * a`, with `q ∈ V` and `a ∈ A`.
- Conjugation by `r` carries `V` and `B` into `U`.
- Each nonidentity point of `A` factors as `x * m * y`, with `x,y ∈ B`
  and `m ∈ M`.
- For each `n ∈ M`, conjugation by `n⁻¹` carries either all of `A` or
  all of `B` into `U`.

It concludes that `r` preserves `doubleCosets U M` by left
multiplication. To see the implemented argument, write the point as
`q * a * n * v`. In the first sign case, move `a` across `n`, leaving
middle factor `r * n`. In the other case, treat `a = 1` separately.
Otherwise substitute `a = x * m * y`, move `x` across `r` and `y`
across `n`, and retain middle factor `r * m * n`.

`closure_subset_doubleCosets` uses left word induction in the subgroup
closure. Its hypotheses are stability under each generator and under
each inverse generator. `generated_subset_doubleCosets` applies it when
the generators are `U`, a subgroup `H ≤ M` that normalizes `U`, and
representatives `R`. For `r ∈ R` it assumes left stability and
`r⁻¹ = h * r` for some `h ∈ H`. The latter identity proves inverse
stability using the already established stability under `H`.
`subgroup_subset_doubleCosets` restricts this covering to any subgroup
contained in that generated subgroup.

Finally, `inf_le_of_doubleCosets` takes `Z ≤ N`, `M ≤ N`, a covered
subgroup `E`, uniqueness of the normalizing middle point in every
`U` double coset, and `Z ∩ M ≤ H`. A point `z ∈ Z ∩ E` has a
factorization `z = u * n * v` with `n ∈ M`. Uniqueness gives `z = n`,
and the kernel inclusion then gives `z ∈ H`.

The provenance is internal: these are direct group identities and
subgroup-closure induction formalizing steps 3 and 4 of the proof sketch
in the published `RootGeneratedCentralizerRankOneStatement` Markdown.
No geometric comparison, factor-pair existence, Weyl presentation,
normalizer uniqueness, or unconditional root-generated centralizer
theorem is proved by this unit.
