# Split-center independence on the identical actual Levi

Worker 835. This derived proof establishes
`Langlands.HarishChandraSchwartz.RationalSemistandard.SplitCenterChoiceIndependenceStatement`
as `splitCenterChoiceIndependence`, over every field universe `u`. Its parameters
are a field, a topology on that field, an affine ambient group scheme, and the
torus morphism indexing the intrinsic semistandard triples. It adds no
local-field or finite-type hypothesis.

For two reductive models `m` and `n` of one intrinsic Levi, the published
`LeviModel.schemeIso` is compatible with their actual inclusions.
Postcomposing a split component of `m` with this isomorphism remains a central
map from a split torus. The published
`Langlands.GroupScheme.IsSplitComponent.exists_factor` factors it through the
split component of `n`; it requires only target affineness, which follows from
the model's connected reductivity. Reversing the models supplies the opposite
factorization.

The private `splitCenter_le_of_factor` specializes such a factorization to
rational points. Subtype extensionality reduces equality in the actual Levi to
equality of ambient rational points. The representability identity
`SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp` then says that the scheme isomorphism followed by the second inclusion is the first
inclusion. Thus each factorization gives inclusion of the literal subgroups.
Antisymmetry proves their equality.

The declaration dependencies are `IsSplitComponent.exists_factor`
(`GroupScheme.Rational.SplitTorusFactorization`), `IsCentral.comp_iso`
(`GroupScheme.CorepresentedComultiplication`),
`SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp`
(`GroupScheme.RepresentedSubgroup`), and the actual model and point-image
definitions in `RationalSemistandardOrbitSections`. All are
published proofs with their actual hypotheses. The target and all its imported
pairs are unchanged.

The source convention is Waldspurger (2003), registered as
`waldspurger-2003-plancherel`, I.1, printed pp.238–239 / PDF pp.4–5:
the split component is the maximal split central torus of the actual Levi.
The subgroup comparison and its proof are derived implementation content.
