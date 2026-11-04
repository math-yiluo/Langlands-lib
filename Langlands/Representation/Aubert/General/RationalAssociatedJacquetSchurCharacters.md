# Schur characters from the actual associated Jacquet isomorphism

This derived supporting construction transports admissibility and identifies
the full-center scalar characters of the actual associated Jacquet module.
It takes an actual smooth isomorphism from that module to the inverse
longest-conjugation pullback of the inducing object. Existence of this
isomorphism remains an input; the construction does not produce a geometric
filtration or prove the rank-one self-association statement.

The generic `smooth_isAdmissible_of_iso_pullback` applies
`Langlands.isAdmissible_comp_continuousMulEquiv` to the original admissible
representation and then `Langlands.isAdmissible_of_equiv` to the inverse of
`SmoothRep.equivOfIso E`. It retains the Library's admissibility convention
for all open subgroups and transports smoothness as well. The two groups
and the representation carrier have independent universes.

`smooth_scalarCharacters_eq_of_iso_pullback` applies the published
`scalarCharacter_eq_of_pullback_equiv` to the actual equivalence underlying
the smooth isomorphism. Nontriviality of the original carrier passes to
the source through the inverse equivalence. This generic lemma keeps the
scalar comparison separate from the much larger rational Jacquet object.

In the rational specialization, `pointInducedJacquetObject` is the actual
normalized Jacquet functor applied to actual normalized induction. The
source Levi is indexed by `I` and the target by `associatedSubset cs I`.
The retained isomorphism uses the inverse of
`associatedLeviConjugationEquiv` for the specified normalizer lift `n` of
`longestRep cs I`. Thus its group map sends an associated-Levi point `m`
to `n * m * n⁻¹`. This is exactly the convention of
`pointAssociatedJacquetIsoOfGeometricFiltration` in
`RationalGeometricFiltrationCollapse`. That published conditional
construction can supply the isomorphism after its actual filtration,
graded-piece and survivor inputs have been provided.

`pointAssociatedJacquet_isAdmissible_of_iso` specializes the generic
admissibility transfer to this isomorphism. It requires inducing
admissibility, with no separate associated-Jacquet admissibility premise.

`InductionTwoJacquetScalarCharacters.second_eq_associated_of_iso` works
for any supplied `InductionTwoJacquetScalarCharacters` pair. It derives
inducing nontriviality from `repLength_eq_one_iff` and `repLength_pos_iff`
and applies `smooth_scalarCharacters_eq_of_iso_pullback` to the actual
associated-Levi equivalence and the pair's two scalar-action laws. The
resulting composition on full centers is definitionally
`associatedLeviCentralCharacter`, giving the claimed equality. The
published scalar-cancellation proof is reused, and there is no assumption
that the scalar characters were chosen compatibly.
In particular, this equality applies to the precise Schur pair used by
`RationalLocalInductionIrreducibility`.

`associatedJacquetScalarCharactersOfIso` constructs the two characters
with `inductionTwoJacquetScalarCharactersOfSchur`, using the transported
associated irreducibility and admissibility. Its value is the actual
scalar-character datum together with the proved conjugation equality.
Inducing irreducibility and admissibility are explicit inputs.

The rational results retain arbitrary field and carrier universes `u` and
`v`, the carrier universe `max (u + 1) v`, canonical `pointTopology`,
connected reductivity, maximal splitness, genericity, standard cocharacters,
radical closedness, actual normalizer and centralizer comparisons, the
actual Coxeter system, root-length and positive-reflection comparisons,
minimality and associated-subset laws. Local compactness and the
nonarchimedean-group structure of the point group are explicit instances.
No local-field valuation, characteristic-zero, split or quasisplit
restriction, maximality of `I`, nonempty root type or non-self-association
assumption is needed for these consequences of the supplied isomorphism.

This unit is derived from the named published transport, scalar-comparison
and admissible-Schur proofs. It invokes no classification, character
independence, geometric-lemma existence, adjointness or cuspidal-support
theorem to establish the retained isomorphism. It does not discharge the
other analytic, structural, coefficient or detection inputs of the local
irreducibility assembly or the exact self-association target.
