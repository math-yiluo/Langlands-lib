# Finite-orbit algebra for the norm--trace comparison

Worker 126 develops internal algebraic helpers for the direct proof of the
Deligne--Henniart top-layer norm--trace congruence. They are derived from
Mathlib finite group actions, finite sums, and normal extension theory.
No local-field estimate is asserted here.

`sum_mem_of_orbit_sums` partitions an invariant finite subset of a finite
group action by its orbit equivalence classes. If the sum of the values of
an arbitrary function on each orbit lies in a supplied additive subgroup,
the sum on the invariant subset lies there too. Its proof rewrites the sum
as a sum over the image in the orbit quotient, identifies each fiber with
its full orbit using invariance, and applies closure under finite sums.

`exists_automorphism_extending_embedding` applies normal lifting to an
embedding of an intermediate field into a normal overfield. The resulting
endomorphism of the overfield is bijective by normality and hence gives
the required automorphism. The field universes are independent and no
normality of the intermediate extension is required.

`sum_action_eq_card_stabilizer_nsmul` counts the multiplicity of each orbit
element when summing over the acting group. It partitions the group by
the fibers of its orbit map and identifies each fiber with the stabilizer
by multiplying by an element carrying the chosen point to that orbit
element. Every fiber sum is therefore the stabilizer cardinality times
the corresponding summand. `OrbitSumDecompositionStatement G Y A` is the
conjunction of these two finite-orbit sum assertions and
`orbitSumDecomposition` proves it.

`normal_embeddings_postcomp_bijective` shows that postcomposition with an
embedding of the normal overfield into an algebraically closed field
induces a bijection on embeddings of the intermediate field. Injectivity
uses the field embedding's injectivity. Surjectivity first extends the
given embedding to the normal overfield and then restricts that extension
back to the normal field.

`algebraMap_norm_eq_prod_embeddings_normal` and
`algebraMap_trace_eq_sum_embeddings_normal` express norm and trace as the
product and sum over embeddings into the supplied normal overfield.
They assume that the intermediate extension is finite and separable;
normality is required only for the overfield. Their proofs map into an
algebraic closure, use Mathlib's algebraically closed embedding formulas,
and reindex by the preceding bijection. The field universes remain
independent.
