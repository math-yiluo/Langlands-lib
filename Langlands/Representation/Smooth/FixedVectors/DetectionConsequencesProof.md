# Proof of generation and length from compact-open detection

Worker 1210, in coordination with Worker 189.

`Langlands.compactOpenDetectionConsequences` targets the internal
`Langlands.CompactOpenDetectionConsequencesStatement.{uG,uV}`. The group
and carrier universes remain independent.

`SmoothRep.fixedVector_of_irreducible_subquotient_detection` starts with a
nonzero actual smooth subquotient `D` of `A`. The published existence theorem
supplies an irreducible actual subquotient `E` of `D`, without assuming
finite length. Subquotient transitivity makes `E` a subquotient of `A`,
so the detection premise supplies a nonzero fixed vector in `E`. Present
`E` by an injection `C → D` and a surjection `C → E`. Compact-open
fixed-vector surjectivity lifts its fixed vector to `C`; the injection
maps the lift to a fixed vector in `D`. If this image were zero,
injectivity would make the lift zero, contradicting the chosen vector in
`E`.

`SmoothRep.fixedVectors_generate_subquotients_of_detection` takes a
subquotient `D` and an invariant submodule `S` containing its fixed vectors.
If `S` were proper, the actual quotient `Q = D/S` would be nonzero.
Transitivity makes `Q` a subquotient of `A`, so detection supplies a nonzero
fixed vector in `Q`. Compact-open fixed-vector surjectivity lifts it to a
fixed vector in `D`, which belongs to `S`. The actual quotient map
therefore sends that lift to zero, a contradiction. This proves generation
without any admissibility or finite-dimensionality hypothesis.

`SmoothRep.fixedVectors_length_of_subquotient_generation` considers a
strict inclusion `S < T` of invariant submodules of `A`. If every ambient
fixed vector in `T` lay in `S`, the pullback of `S` inside the actual
representation on `T` would contain all its fixed vectors. Since `T` is
an actual subquotient of `A`, the generation hypothesis would make this
pullback top. That would give `T ≤ S`, contradicting strictness.
Thus there is a fixed vector in `T` outside `S`. The published
`fixedVectorsStrictInclusionLength` now gives both the actual composition
length bound and finite length over the actual group algebra. Only this
last step needs finite dimension of the ambient fixed space.

The final theorem pairs these three deductions. Its provenance is the
published irreducible-existence, subquotient-transitivity, compact-open
surjectivity, and fixed-vector chain results together with the explicit
actual quotient argument above. It abstracts the final corollary and chain
arguments of Renard VI.6.3; no equality with an unimplemented source object
is assumed.

The proof includes the zero representation. It does not construct a
compact open subgroup or establish irreducible detection on actual
reductive rational points. The final Howe implication, its converse, the
other source intermediate assertions, and the specially chosen subgroup
bound remain separate obligations.
