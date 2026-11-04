# Actual relative roots supported by subgroup functors

This is a derived construction on the Library's actual group schemes and
all-test subgroup functors. It supplies root indexing for later intertwining
regions; it asserts no convergence theorem.

Let `i : S.toGrp ⟶ G` be an actual morphism over an arbitrary field, with `G`
affine over the field. `subgroupRelativeRoots i F` is the conjugation-action
weight support of the actual subgroup functor `F`, with the zero character
removed. A supporting vector is nonzero in the existing actual Lie kernel,
belongs to the actual action weight space, and lies in `F` on the dual-number
test scheme. This definition does not identify arbitrary subgroup functors
with algebraic radicals, and requires no representability or stability of `F`.

The elementary lemmas remove zero, preserve support under actual subgroup
inclusion, and embed every such support in `relativeRoots i`. For the whole
group the support is exactly `relativeRoots i`. If `S` is split and `G` is
locally of finite type, the published finite-dimensional Lie weight
decomposition makes the root set finite, so every subgroup support is finite.
No reduced root system is substituted for the actual relative roots.

For smooth affine `G` and split `S`,
`actionWeightSupport_dynamicUnipotent` proves that the complete support of
`Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)` is
`positiveRelativeRoots i ν`. The proof uses the published exact Lie-image
theorem `dynamicUnipotent_semigroupData` and the support bound supplied by
`dynamicUnipotentGenerator`. The general exact-Lie-image support comparison
then identifies the support with the intersection of the ambient support and
the positive pairing semigroup. The published ambient comparison identifies
that intersection with the actual positive roots. Positivity excludes zero,
giving `subgroupRelativeRoots_dynamicUnipotent`. This route requires neither
`SemigroupRealizationStatement` nor connectedness or reductivity of `G`.

`intertwiningRelativeRoots i U Uop'` intersects the two actual nonzero
supports. It is a subset of the actual root set and is finite under the same
splitness and finite-type hypotheses. The second subgroup is an explicit
input: the definition alone does not make it the opposite radical of any
parabolic. For the actual dynamic subgroups of `ν` and `-η`,
`intertwiningRelativeRoots_dynamic` identifies this intersection with all
actual roots having positive pairing with `ν` and negative pairing with `η`.
Multipliable relative roots are retained.

All proofs are direct consequences of the imported actual-support, dynamic
Lie-image and root-finiteness results. The later application to Waldspurger's
`Σ(P) ∩ Σ(opposite P')` must identify the actual split component and the two
radicals; this module supplies no such identification for unspecified inputs.
