# Dense unitary irreducibility of actual common-Levi normalized induction

`Langlands.Plancherel.ActualCommonLeviV3.denseUnitaryIrreducibility` proves
`DenseUnitaryIrreducibilityStatement` at independent field and inducing
carrier universes `u` and `uV`. For every cocharacter with the given common
Levi, it gives density of the irreducible normalized inductions in the
full unitary unramified parameter group.

## Implemented proof

1. `LeftHaarQuotientUnitarity` derives an invariant positive form from the
   supplied square-integrable coefficient norms. It polarizes the norms
   on the supplied measurable quotient, uses left Haar invariance on
   the smooth dual, and pulls the resulting form back through the smooth
   bidual. `dynamicCentralizer_compactOpenCofinal` supplies the compact
   open cofinality used in that argument.
2. For the chosen cocharacter, `DynamicCommonLeviPresentations.parabolicData`
   constructs a represented parabolic on the fixed parameter scheme
   using the split component supplied by `IsActualSplitCenter`. Its
   geometric radical gives the actual multiplication isomorphism.
   Pullback through `parameterHomeomorph` transports irreducibility,
   admissibility and the invariant positive form to the inducing
   representation of the scheme's rational points.
3. `exists_generic_leviInduction_isIrreducible_of_unitary` gives a nonzero
   polynomial whose principal open consists of irreducible inductions
   at norm-one twists. In this lemma, a proper nonzero summand of the
   admissible unitary induction would give a nonzero map from a quotient
   back into the induction. First adjointness transfers an inducing
   exponent to the quotient's Jacquet module, contradicting the
   published quotient exclusion theorem on the principal open.
4. `polynomialToLaurent` and `rationalCanonicalUnramifiedLaurentAlgebraEquiv`
   turn the polynomial into a regular function on the actual parameter
   group. Their evaluation formulas identify its nonvanishing locus
   with the principal open. The principal open has a point by
   `dense_rationalUnramifiedPrincipalOpen`, so the function is nonzero.
   `dense_unitary_regular_nonzero` gives density of its nonvanishing
   on the unitary group.
5. `leviInduction_isIrreducible_iff_of_pointImage` transports irreducibility
   from that dense set to the actual dynamic induction. The presentation
   identifies the parabolic, Levi and radical point images with the
   literal subgroups. The carrier comparison is the identity linear
   equivalence. The represented twist evaluates the same character
   as the literal twist, since transport through `parameterHomeomorph`
   uses the inverse map on character arguments.

## Relation to the sources

The target's provenance is Waldspurger's Proposition IV.2.2(i) and the
opening of IV.3, printed pp. 284–285. The implemented proof obtains
the principal open from the Library's quotient exclusion theorem
derived from Konno's Theorem 4.2, and gives the unitary density conclusion
through regular function nonvanishing. The supporting
`InducedTwistUnitaryGenericIrreducibility` module records the
exclusion and semisimplicity argument.
