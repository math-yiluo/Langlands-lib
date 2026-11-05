# Torus containment from actual opposite-root factor pairs

`torusLiftOfOppositeFactorPairs` constructs an actual homomorphism from a split
closed torus `i : T → G` to a closed subgroup `j : H → G` of a semisimple group
over an arbitrary field. It assumes that `H` contains the full intrinsic root
subgroup functor of every actual relative root of `i`, and that
`RelativeRoot.HasOppositeFactorPairs i` holds. The companion equality
`torusLiftOfOppositeFactorPairs_comp` states that composition with `j` is `i`.
No maximality assumption on the torus, root reducedness, or restriction on the
characteristic is needed.

The implemented proof first establishes
`RelativeRoot.IsOppositeFactorPair.torusCommutatorEnd_mem`. A normalizing product
of one root point and two opposite-root points lies in any subgroup functor
containing both root functors. Torus stability of those functors keeps the torus
conjugate of each factor in the same subgroup. The commutator of the product
`n` with a torus point `t` is `n * (t * n * t⁻¹)⁻¹`, so also belongs to the
subgroup, on every test scheme.

`IsRootDatumOf.coroot_mem_of_torusCommutators` uses a specified reflection
representative, requiring only its commutators with torus points to land in
the closed subgroup. The reflection negates its coroot, so its commutator
endomorphism sends the coroot to minus twice itself. The imported saturation
lemma removes this nonzero integer by faithfully flat descent along
multiplication on the multiplicative group. This argument also applies in
characteristic two; it does not divide by two in the ground field.

`IsSemisimple.range_torus_le_of_oppositeFactorPairs` chooses a nonidentity
rational point in every actual root functor using the published unconditional
rational nontriviality theorem. The explicit opposite-pair premise supplies a
normalizing product for each choice. The imported factor-pair consequences prove
that each product flips its root and determines an integral coroot with the
full character reflection formula. These data construct an actual root datum.
Negation of roots follows from the actual normalizer action, and is not a
separate premise.

Semisimplicity makes the actual roots span the rational character space.
The imported root-datum results then give finite index of the integral coroot
span. The commutator argument puts each coroot in the submodule of cocharacters
landing in `H`. Finite index and saturation put every cocharacter in that
submodule. Split-torus coordinates yield full all-test containment of `i` in
`j`. Finally, representability of the closed subgroup factors `i` through `H`,
giving the stated actual homomorphism.

This is a derived internal construction from the imported torus, root-functor,
factor-pair and semisimple-lattice results, rather than a new source definition.
Containment and all equalities use all test schemes, including nonreduced tests.
Opposite-pair existence remains an explicit structural premise; this module
proves neither that premise nor unconditional root generation, and does not
complete the almost-simple-generation task.
