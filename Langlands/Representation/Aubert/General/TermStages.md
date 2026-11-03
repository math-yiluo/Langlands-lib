# Exact-K0 term transitivity from normalized stages

This internal construction combines two supplied actual normalized stage
isomorphisms. Its ambient group is locally compact and nonarchimedean, with
independent group and carrier parameters `uG` and `uV`. The representations have
the published saturated carrier universe `max uG uV`. It takes a fine and a
coarse actual semidirect decomposition, closed radicals `U₀` and `U₁`, a closed
coarse Levi `M₁`, an inclusion `M₀ ≤ M₁`, and the actual restricted fine
semidirect decomposition inside `M₁`. It proves neither stage isomorphism;
those must be proved for the rational family before the helper discharges
its term-transitivity obligation.

`stagedInductionJacquetFunctor` is the actual four-functor composite: normalized
Jacquet restriction to `M₁`, normalized Jacquet restriction to the literal
`M₀.subgroupOf M₁`, then the two normalized inductions in reverse order.
`inductionJacquetStagesIso` compares it with the direct fine
`inductionJacquetFunctor`. The supplied induction isomorphism is
`leviNormalizedInductionFunctor ⋙ normalizedInductionFunctor h₁ ≅
normalizedInductionFunctor h₀`; the supplied Jacquet isomorphism is
`jacquetFunctor h₁ ⋙ leviNormalizedJacquetFunctor ≅ jacquetFunctor h₀`.
They compare the actual published functors, including their normalization
characters and canonical subgroup transports.

The private `inversePullbackIso` has identity linear maps. Its equivariance is
the equality `e.symm (e h) = h` for the canonical continuous group equivalence,
and its naturality is equality of the unchanged underlying linear maps.
Insert its inverse between inner restriction and inner induction. Whiskering
the supplied induction isomorphism collapses the two inductions; whiskering
the supplied Jacquet isomorphism then collapses the restrictions. Thus the
final natural comparison is constructed and no compatibility with arbitrary
subgroup families is asserted.

`inductionK0_comp_leviTerm_comp_jacquetK0` additionally takes the existing
`ParabolicFiniteLength` premises for each decomposition, at exactly these
carrier universes. The published `PreservesFiniteLength.comp` and
`PreservesFiniteLengthShortExact.comp` build the preservation proofs for the
composites. `FiniteLengthGrothendieckGroup.map_eq_of_iso` applies the constructed
natural isomorphism, and four explicit uses of
`FiniteLengthGrothendieckGroup.map_comp` identify its maps with the four actual
induction and Jacquet maps. Associativity gives precisely the coarse induction,
inside-Levi term, coarse Jacquet composite equal to the fine term. These
published map laws themselves compare actual finite-length object classes
and extend by `hom_ext_object`; the result therefore holds on the whole exact
Grothendieck group and retains all nonsplit short-exact-sequence relations.

Provenance is internal: the proof uses the actual functor definitions and
exact-K0 map laws in `General.AlternatingOperator` and
`Smooth.FiniteLengthGrothendieckFunctor`, plus elementary natural-isomorphism
whiskering. It invokes no classification, character independence, geometric
lemma, adjointness or cuspidal-support proof. The two stage isomorphisms remain
explicit inputs; this pair alone does not prove rational involutivity.
