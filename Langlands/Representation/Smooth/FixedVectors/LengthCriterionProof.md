# Proof of the elementary fixed-vector reductions

Worker 1210. Worker 189 contributed the agreed interface and the reuse route
through the published actual composition-length criterion.

The theorem `Langlands.fixedVectorLengthReduction` proves exactly the published
proposition `Langlands.FixedVectorLengthReductionStatement`. Its three universe
parameters for coefficients, the group and the vector-space carrier are
independent. The proof uses no nonzero-carrier premise.

The source context is Renard VI.6.3, French version dated 9 July 2026, printed
pages 178–179 / PDF pages 184–185, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The forward proof on PDF185 chooses a subgroup fixing finite generators and
bounds submodule chains by chains of fixed-vector spaces. These are internal,
more general algebraic reductions of those elementary steps. They do not
prove or assume the unrestricted rational-point Howe statement.

`eq_top_of_fixedVectors_le_of_generators` first proves that an invariant subspace
containing a fixed generating family is the whole representation. The actual
group-algebra span lies in its actual group-algebra submodule. The span is the
whole module, so the published order isomorphism from subrepresentations to
group-algebra submodules gives equality with the whole representation.

`commonFixedGenerators` uses `Module.Finite.exists_fin` on `ρ.asModule` to
choose a finite family of actual group-algebra generators, and transports the
family to the original representation carrier with `ρ.asModuleEquiv`.
Smoothness gives one open stabilizer per generator. Their finite infimum is an
open subgroup fixing every generator; the empty family is allowed and its
infimum is the whole group. The same generators are fixed by each smaller
subgroup. The preceding span argument proves the asserted generation property.
This part works over any commutative coefficient ring and does not require a
topological-group instance.

`fixedVectorsStrictInclusionLength` sends an actual subrepresentation `S` to
the inverse image of `S.toSubmodule` under the inclusion of `fixedVectors ρ K`
in the ambient carrier. This is precisely the intersection with the fixed
vectors, regarded as a submodule of the fixed-vector space. A detection
witness for `S < T` lies in the upper inverse image and outside the lower one.
Consequently these inverse images, and then their finite dimensions, strictly
increase along every strict chain. All dimensions are bounded by the dimension
of the ambient fixed-vector space. Mathlib's natural-number strict-chain
inequality therefore bounds the number of inclusions by that dimension.

The published
`Langlands.LengthCriterionProof.hasCompositionLengthAtMost_of_bound` supplies
an actual composition series within this bound.
`Langlands.objectCompositionLengthCriterion` then gives finite length over
`MonoidAlgebra R G` of the actual `ρ.asModule`. Both are imported from
`Langlands.Representation.Filtration.LengthCriterionProof`; no categorical
or alternate notion of finite length replaces the actual module predicate.

The reductive-group detection argument and the choice of a normal compact open
subgroup with simultaneous Iwahori decompositions remain separate obligations.
In particular the length conclusion here is conditional on detection; the
unrestricted Howe target and its imported Lean/Markdown pairs are unchanged.
The exact VI.6.3 intermediate assertions and the source's bound for its specially
chosen compact subgroup are not claimed as consequences of this helper alone.
