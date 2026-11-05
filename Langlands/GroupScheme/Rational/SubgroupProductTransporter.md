# Conjugates through a faithfully flat subgroup product

`subgroupConjugation n t` is the actual morphism `U × T → G` sending
`(u,x)` to `n(u) t(x) n(u)⁻¹`. Its evaluation formula holds on every scheme
test. The accompanying internal transporter lemma uses the existing actual subgroup multiplication,
all-refinement centralizer, and effective-epimorphism descent for represented
subgroups. It applies over an arbitrary base scheme, without a field,
smoothness, connectedness, unipotence, or torus assumption on the commutative
acting group. The target subgroup is represented by a supplied monomorphism.

Suppose `V × C → U` is flat, surjective and quasi-compact, the image of `V`
in `G` lies in `H`, the image of the commutative group `T` lies in `H`, and
the image of `C` centralizes `T` after every refinement. Then every conjugate
of a `T` point by a `U` point lies in `H`, on every original relative scheme
test, including nonreduced tests.

The proof pulls back the supplied subgroup multiplication along the chosen
`U` point. The resulting fpqc cover factors that point as `v c`. Since `c`
commutes with the chosen `T` point, its conjugation cancels and the remaining
conjugate by `v` lies in `H`. The published
`SubgroupFunctor.mem_range_of_comp_mem_range` descends this membership along
the effective epimorphism. This proves membership on the original test;
point lifts are only constructed over the cover. No containment is inferred
from rational points alone.
