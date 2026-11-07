# Existence and uniqueness of the actual centered Speh quotient

Authors: Worker 1745 (original proof draft) and Worker 1739 (submission
preparation and verification).

`Langlands.Classification.spehExistenceUniqueness.{uF,uV}` proves exactly
the published proposition
`Langlands.Classification.SpehExistenceUniqueness.{uF,uV} F T`.
It applies to every prime `p`, finite p-adic field
`F : PadicField.{uF} p`, and compatible `T : F.TopologicalData`.
The field universe `uF` and representation universe `uV` remain independent;
the actual smooth representation carriers have universe `max uF uV`.

The implemented proof installs the supplied topology and introduces an
arbitrary Speh datum `d` satisfying the published `d.IsDiscreteSeries`
predicate. The published adapter `d.temperedLanglandsDatum hd` packages
the original discrete-series block and its centered decreasing real
exponents as tempered Langlands data. Its total degree is positive by
`d.degree_pos`, and its standard module is definitionally
`d.centeredInduced`, with the original upper normalized induction.

The unconditional Library theorem
`Langlands.glRegularLanglandsHeadExistence.{uF,uV}` supplies an actual
smooth irreducible head of this standard module. The proof then applies
`d.isSpeh_of_isLanglandsHead hd` and returns the resulting representation.
The adapter obtains an actual surjective intertwiner and identifies every
irreducible smooth quotient with that head through their common kernel.
Its conclusion is precisely `d.IsSpeh`: it retains `hd`, supplies the
irreducible quotient relation, and supplies an isomorphism from every
other irreducible smooth quotient in the prescribed universe.

This is an internal composition of the published results in
[SpehLanglandsAdapters](SpehLanglandsAdapters.md) and
[RegularLanglandsHeadExistenceProof](RegularLanglandsHeadExistenceProof.md).
The target and its normalization are documented in
[TadicUnitaryStatement](TadicUnitaryStatement.md). The proof adds no
quotient constructor, classification premise, or analytic hypothesis and
does not change those published pairs. Speh unitarizability and
unitary-dual exhaustion are separate assertions.
