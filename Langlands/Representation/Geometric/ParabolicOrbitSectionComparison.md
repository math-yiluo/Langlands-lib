# Full intermediate section and target refined projection

This internal construction identifies the action on the actual orbit coefficient
quotient along the full intermediate section. It uses the supplied target
intersection refinement to factor its source coordinate through the actual
refined Levi projection. It asserts no integral comparison or final normalized
natural isomorphism.

For an arbitrary commutative ring `F`, block shapes `B, C`, permutation `w` and
target refinement `R`, assume the full target intersection-refinement triple
`hR`. Let `K = parabolicOrbitStagesQuotient F B C w`. The equivalence
`parabolicOrbitStagesRefinedEquiv` identifies `K` with
`refinedParabolic F C R`: it composes `parabolicOrbitStages_comap_section` with
`hR.1` and keeps the same element of `C.Levi F` in both directions.
`parabolicOrbitRefinedSection` is the actual target Levi section into the orbit
stabilizer, with its domain relabeled by this equivalence.

The homomorphism `parabolicOrbitRefinedSourceCoordinate` applies inverse
conjugation followed by the actual source Levi projection to that section.
Its restriction to `refinedUnipotentRadical F C R` is trivial. Indeed,
`mem_refinedUnipotentRadical` and `hR.2.2` put the underlying element in
`sourceUnipotent F C B w⁻¹`; inverse conjugation therefore lies in the actual
source unipotent subgroup. By the definition of that subgroup as the image
of the source projection kernel, the source coordinate is one.

On the target refined Levi, `hR.2.1` identifies the section with
`parabolicOrbitIntersectionSection`. The published
`parabolicOrbitToSourceLevi_intersectionSection` computes its source coordinate
as inverse intersection-Levi conjugation. Applying the published
`refinedDecomposition`, whose factors are the radical part and the projected
Levi section, proves `parabolicOrbitRefinedSourceCoordinate_factor` on every
element of the full target refined parabolic.

`parabolicOrbitTargetLeviProjection` transports the target refined projection
back to the actual target intersection Levi. Its composite with inverse
`intersectionLeviConjugation` is `parabolicOrbitSourceLeviCoordinate`, valued
in the actual source intersection Levi. The theorem
`parabolicOrbitToSourceLevi_stagesSection` identifies its underlying source
Levi element with the original section coordinate on every element of `K`.
With a full source refinement triple `hS`,
`parabolicOrbitSourceRefinedCoordinate` relabels this same source element in
`refinedLevi F B S`.

For a complex representation `ρ` and character `χ` trivial on the actual source
intersection radical, `parabolicOrbitFullCoefficientAction` is the actual
stabilizer action on its radical coinvariants, restricted along the full
intermediate section. `parabolicOrbitFullCoefficientActionEquiv` identifies it
with the source Jacquet action twisted by the restricted `χ`, transported by
inverse intersection conjugation and inflated along the target projection.
The linear equivalence is exactly `parabolicOrbitCoefficientEquiv`. On every
vector representative, the factorization above and linearity of the quotient
map prove equivariance. Its representative law keeps the vector, and its
naturality for every coefficient intertwiner is the previously proved
coefficient naturality, with independent carrier universes. The separate
`parabolicOrbitNestedCoefficientEquiv_projected_section_mk` gives the same
projected formula on the actual nested coefficient quotient used in stages.

For any topology on `F`, `parabolicOrbitStagesRefinedEquivContinuous` bundles
the relabeling with its induced subgroup topologies. If `F` is a topological
ring, the target projection and both source coordinate maps are continuous,
by continuity of the actual refined projection, inverse intersection
conjugation and subtype inclusions.

For every prime, actual finite p-adic extension and supplied compatible
topological data, retain both full refinement triples. For `l ∈ K`, write
`a(l)` for its source Levi coordinate and `aS(l)` for the same element in the
source refined Levi. The character `parabolicOrbitSectionCharacter` is

`γ(l) = leviHalfModulus B (a(l)) * refinedLeviHalfModulus B S (aS(l))`.

Both factors are positive halves. The first is the original source induction
half, and the second removes the inverse half in normalized source refined
Jacquet. The private representative computation
`sectionCharacter_normalized_mk` expands `normalizedRefinedJacquet_mk` and
cancels that second positive half with its inverse.

`parabolicOrbitFullRefinedCoefficientActionEquiv` uses the actual
`parabolicOrbitRefinedCoefficientEquiv` as its linear equivalence. It intertwines
the full stabilizer quotient action with normalized refined Jacquet pulled
back by `aS` and twisted by `γ`. The equivariance proof is quotient induction,
the full coordinate factorization and the preceding scalar identity. Its
representative law and naturality hold for every vector and every original
intertwiner, using the actual `normalizedRefinedJacquetMap` and independently
quantified carrier universes. The theorem
`parabolicOrbitNestedRefinedCoefficientEquiv_projected_section_mk` proves the
same normalized section formula on the actual nested coefficient quotient;
it does not introduce a separate nested quotient action.

No positive-rank, minimal-permutation, smoothness, dimension or length
condition is needed for these coefficient constructions. The field and
coefficient universes remain independent. The displayed character `γ` is an
intermediate factor, not a residual twist claimed for the final comparison.
Identifying the actual integral Haar ratio, canceling it with the target and
source normalization factors, obtaining the compact/smooth induction
comparison and assembling the final natural orbit-functor isomorphism remain
separate obligations. The provenance of this pair is the internal derivation
from the actual subgroup definitions, full refinement equalities,
`refinedDecomposition`, and the previously constructed coefficient transports.
