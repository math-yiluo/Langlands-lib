# Integral Iwasawa families from supplied-model maximal compactness

Worker 4256.

This internal composition constructs simultaneous good arithmetic models and
discharges relative parabolic quotient existence using published Library
proofs. It reduces the complete
`Langlands.Global.IntegralIwasawaFamily.ExistenceStatement.{u}` to the one
explicit remaining premise
`Langlands.GroupScheme.IntegralModel.MaximalCompactStatement.{u}`.
It does not prove that premise or the unconditional family existence target.

`goodModelData` takes precisely a number field `F : Type u`, an actual group
scheme `G` with `IsConnectedReductive G`, and an actual homomorphism
`p : P ⟶ G` with `IsParabolicSubgroup p`. It returns a finite set `S` and
the original `ReductiveParabolicSpreading.ModelData` over the actual ring
`(S : Set (FinitePlace F)).integer F`. All its fields are supplied, including
the prescribed generic isomorphisms, the extension of `p`, closedness,
ambient reductivity, subgroup smoothness, and all three field-valued fibre
conditions. The construction specializes `modelDataOfSpreadingStatements`
with the proved `genericReductivitySpreading` and `parabolicDynamic`.
Neither structural statement remains a premise.

`relativeParabolicQuotient` proves the existing relative quotient proposition
by applying `RelativeParabolicQuotient.existenceStatement_of_dynamic_and_ambient`
to the published `parabolicDynamic` and `selfNormalizingProperAmbient`.
The imported construction already discharges its proper ambient criterion.
The result retains every commutative coefficient ring, every original
subgroup and every test scheme in that proposition.

`existenceStatement_of_maximalCompact` keeps maximal compactness as an explicit
premise. For each field, group and parabolic in the original family target,
it derives affineness and local finite type from connected reductivity,
constructs `goodModelData`, and chooses the existing
`FiniteTypeIntegralFamily.subgroup F G`. This is one family, chosen before
the later adelic point and regular function.

For a place outside the constructed finite set, the proof uses the original
completion `FiniteCompletion F v`, its existing topology and
`FiniteCompletion.valuativeRel v`. The theorem
`connectedReductiveFieldExtensionStatement` gives connected reductivity of
the ambient generic group. The actual canonical-integer model is
`IntegralModelCompletions.canonicalModel`; connected reductivity of its actual
special fibre follows from `canonicalModelData_specialFibre`. Applying the
explicit maximal compactness premise gives equality with every compact
overgroup in the existing rational-point topology.

`ModelLocalConditions.of_quotientStatement` transports that maximality to
the original coefficient-point carrier and supplies the literal
parabolic-left covering using `relativeParabolicQuotient`. The imported
covering proof uses the proper quotient and the established integral torsor
lifting theorem. Finally `isIntegralIwasawaFamily_of_models` gives all three
clauses of the original predicate for this same family: compactness,
maximality and covering at cofinitely many places; cofinite absorption for
every actual adelic point; and cofinite uniform integrality for each regular
function. The latter two conclusions use the published fixed-family
theorems. No new carrier or topology is introduced.

The universe `u` is arbitrary. Non-split, anisotropic and improper-parabolic
cases are retained. The original statement and all its imports are
unchanged. The provenance is entirely internal composition of the named
Library constructions and proofs; no additional assertion from external
literature is introduced. Independent proof and publication of the maximal
compactness premise are still needed for the unconditional task.
