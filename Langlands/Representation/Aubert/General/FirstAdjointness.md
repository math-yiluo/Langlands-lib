# First adjointness for the actual general normalized functors

Worker 1216 implements the derived internal equivalence
`Langlands.Aubert.General.FirstAdjointness.equiv`. It identifies actual
intertwiners from a smooth representation `A` into normalized induction of `σ`
with actual intertwiners from the normalized Jacquet module of `A` to `σ`.
The group universe `uG` and the two carrier universes `uV` and `uW` are
independent. Induction has its existing carrier universe `max uG uW`.

The input is an actual semidirect decomposition `P = M ⋉ U` of subgroups of a
locally compact nonarchimedean group, closedness of `U`, and the explicit
predicate `IsUnimodularModulus U hU`. Neither representation is required to have
finite length or be admissible. No quotient compactness, projection continuity,
geometric lemma, classification, character independence, cuspidal support
theorem, or supplied adjunction is assumed.

The construction is an internal consequence of the published actual functors
and quotient maps, rather than a new reading or assertion about the scope of an
external source. Its declaration dependencies are:

- `Jacquet.CharacterReciprocity.evaluation`, `evaluation_translate` and
  `evaluation_covariance` from `Jacquet.ReciprocityProof` supply evaluation at
  the identity and its covariance before quotienting.
- `Jacquet.Localization.lift`, `mk_surjective` and `hom_ext` descend and
  compare linear maps on the actual quotient by the span of `ρ(u)v - v`.
- `General.closedHalfCharacter_unipotent`,
  `IsSemidirectDecomposition.projection_unipotent` and `projection_levi`
  show triviality on `U` and the exact action on the Levi.
- `General.inducingRepresentation_jacquet_eq` identifies the inducing action
  of `i(r A)` with the actual unnormalized quotient action of `P`. This includes
  the published semidirect-projection calculation and cancellation of the
  positive and inverse half moduli.
- `smoothLift` restricts the covariant orbit map to the actual smooth vectors.

The forward map evaluates at `1`, descends through the literal localization at
the trivial character, and cancels the half moduli to obtain an `M`-intertwiner.
For the inverse, a Jacquet intertwiner `f` gives the orbit function
`g ↦ f([ρ(g)v])`. The equality of inducing representations proves its covariance.
Smoothness of `A` puts the orbit functions in the actual normalized smooth
induction. The two composites are identities by evaluation of a translate and
`ρ(1) = 1`. Linearity is checked after the surjective quotient map.
`equiv_mk` and `equiv_symm_eval` record the exact formulas.

This is a general normalized adjunction input for the rank-one program. It
does not establish the geometric expansion, nonvanishing of constituent Jacquet
modules, the rational-point unimodularity input, or the complete proposition
`RationalRankOneJacquetModulesStatement`. When the actual `U` is a limit of
compact subgroups, the published
`General.isUnimodularModulus_of_isLimitOfCompactSubgroups` supplies its
unimodularity hypothesis; applicability to a rational-point family remains a
separate obligation.
