# Finite-length central action algebras

This is an internal algebraic input for the finite-length converse in Renard
VII.3.3. It is derived from the Library's sigma-compact Schur theorem and the
finite-length module induction principle; it is not a new source translation of
VII.3.3.

`FiniteLengthCentralActionStatement` says that for a sigma-compact topological
group `G`, a smooth complex representation `ρ` whose group-algebra module has
finite length, and any homomorphism from a commutative group `A` to the center of
`G`, the faithful action quotient of `ℂ[A]` is finite dimensional over `ℂ`.
The group, representation carrier and central group have independent universe
parameters. There is no topology assumption on `A` and no admissibility
assumption on `ρ`. The representation carrier need not be finite dimensional.
The theorem `finiteLengthCentralAction` proves precisely this statement.

The stronger helper `finite_hom` proves finite dimensionality of intertwiner
spaces from a smooth finite-length representation to any finite-length
representation of `G`. The two carrier universes are independent; smoothness
of the target is unnecessary. For two simple representations, any nonzero
intertwiner is an equivalence, and the published countable-dimensional Schur
theorem makes all intertwiners scalar multiples of that map. Its countable-rank
hypothesis follows from smoothness of the source and sigma-compactness of `G`.
The zero-Hom case is handled separately.

For an exact sequence of representations, the Hom sequence is exact at its
middle term in either variable. The source-extension helper factors a map
annihilating the subobject through the quotient, using the group-algebra
module quotient. The target-extension helper factors a map landing in the
kernel through the injected subobject. Finiteness of the outer Hom spaces then
implies finiteness of the middle Hom space by finite generation in an exact
sequence. Induction first on the target's composition length with simple
source, then on the smooth source's composition length, proves `finite_hom`.
Module representations and their canonical bijective intertwiners transport
this result to the original representation actions. Subobjects and quotients
of the smooth source remain smooth by the published transfer results.

`centralActionSpan_finite` places the span of the actual central operators in
the range of the linear map from intertwining endomorphisms to all linear
endomorphisms. That range is finite dimensional by `finite_hom`.
`finite_actionQuotient` then uses the published injection of the faithful
commutative action quotient into the actual operator span.

This unit does not prove finite-length preservation by Jacquet or induction
functors, or finite length of the full geometric pieces in VII.3.3. Those are
separate remaining inputs when applying it to those pieces. It does not prove
the exact `PQRegularityLemmaStatement`.
