# Actual Bernstein functors and their independent properties

Worker 132. Supporting derived content for Task 5419, using Renard 2026,
VI.7.2 second Lemma, printed pp.182–183 / PDF pp.188–189, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

`bernsteinJacquetFunctor`, `bernsteinInductionFunctor`, and
`bernsteinRestrictionFunctor` name the literal functors in the closed target,
retaining independent field and carrier universes and actual standard subgroups.
The last construction takes a supplied family of cuspidal-part functors.

`piCoproductFunctor_faithful` is an internal categorical helper. A family of
faithful component functors remains faithful after taking a coproduct in a
category with zero morphisms. Composing an equality of coproduct maps with each
injection and cancelling the target injection recovers each component map;
these injections are split monomorphisms. The index type may be empty.

`bernsteinInductionFunctor_faithful` applies that helper to actual normalized
induction composed with the full cuspidal inclusions. Published compact local
sections give faithfulness of normalized induction when the Levi projection is
continuous. Its continuity for every standard parabolic is discharged by the
published dynamic standard-cocharacter comparison.

The internal exactness helpers connect the concrete short exactness predicate
used in the target to categorical short exactness. In
`smoothShortComplex_shortExact_iff`, the forgetful functor to modules preserves
categorical short exact sequences. Conversely, injectivity and surjectivity
give monicity and epicity, while faithful exact reflection gives exactness from
the equality of the linear range and kernel.
`smooth_comp_eq_zero_of_isShortExact` obtains a zero composite from that
range–kernel equality.

`shortComplex_shortExact_of_evaluation` proves categorical short exactness of
a diagram of short complexes from its evaluations: pointwise monicity and
epicity give monicity and epicity of the natural transformations, and
evaluation functors jointly reflect the kernel limit.
`finiteCoproduct_map_isShortExact` then applies this fact to a finite discrete
diagram of smooth representations. Finite coproduct and product functors are
naturally isomorphic in the abelian category, so the coproduct functor preserves
finite limits as well as colimits. The concrete–categorical bridge transfers
the resulting short exactness back to the concrete predicate. This argument
also covers an empty index type.

`bernsteinInductionFunctor_map_isShortExact` uses that coproduct helper for the
literal functor `I`. Each component is short exact by the published exactness
theorem for normalized induction, applied after the full cuspidal inclusion.
The standard-cocharacter results supply closedness of the actual standard
parabolic and continuity of its Levi projection. The local-field topology and
affineness of the actual ambient group supply Hausdorffness; the assumed
nonarchimedean group structure supplies cofinal compact open subgroups. There
is no additional structural hypothesis.

`bernsteinJacquetFunctor_map_isShortExact` applies actual Jacquet exactness.
The published dynamic unipotent compact-containment theorem supplies its
compact-limit hypothesis. There is no cuspidal decomposition hypothesis.

The named functors are abbreviations or constructions from the published
target. The categorical helpers and the proofs in this module are derived
infrastructure for its faithfulness and exactness clauses; they do not add
independent assertions to the cited source. This module does not prove
reflector existence, the remaining properties of `R`, or the entire closed
target.

The local rational-point topology instance is explicitly named
`bernsteinFunctorPropertiesPointTopology`. Together with the explicit
instance name in `BernsteinCuspAdjunction`, this allows the functor-properties
and `BernsteinLeviCuspidalSplitting` modules to be imported together without
declaration-name collisions. Its value remains the actual `pointTopology`.
