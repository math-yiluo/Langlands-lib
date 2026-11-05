# Cuspidal extraction from supplied actual rational geometric filtrations

Workers 321 and 1553 provide this internal composition for actual rational
cuspidal Jacquet-factor extraction. It assembles the actual geometric-term
comparisons and the actual finite-filtration extraction. The filtration,
its actual normalized grade isomorphisms, and proper-target exclusion remain
explicit hypotheses. This unit does not prove
`RationalCuspidalJacquetFactorExtractionStatement`.

`PointGeometricCuspidalGradeDichotomy` describes the required alternative for
each actual geometric term of `r_J i_I` on an inside-Levi cuspidal datum `sigma`.
Either every irreducible inside-Levi cuspidal object on `M_J` is excluded as an
actual subquotient, or the entire term is actually isomorphic to conjugation
of `sigma` along its supplied normalizer lift. The second branch retains that
same lift, its dependent Levi membership witness, and its actual root
association. The definition asserts no geometric-filtration theorem.

`pointGeometricCuspidalGradeDichotomy_of_geometry_exclusion` proves this
alternative from `PointCuspidalExtractionGeometry` and
`PointProperTargetGeometricTermExclusion`. If the intrinsic source intersection
is proper, source cuspidality makes the actual term a subsingleton.
`isCorollaryLeviCuspidal_iff_isLeviCuspidal` converts between categorical zero
and carrier subsingleton in this application. The published elementary
`SmoothRep.not_isSubquotient_of_subsingleton` then excludes every irreducible
factor. If the source is full and the target is proper, the explicit
proper-target exclusion supplies the first branch. If both are full, the
geometry supplies actual root association and the actual entire-term
isomorphism along the identical normalizer lift.

`pointCuspidalJacquetGradedPieces_of_geometricTerms` takes an actual finite
zero-to-full filtration of a smooth object `A` on `M_J` and actual smooth
isomorphisms from all its grades to geometric terms on `sigma`. Each grade
comes with its own minimum representative, normalizer lift, quotient equation,
and source and target decomposition witnesses. The proof transports exclusion
using `SmoothRep.IsSubquotient.of_iso_right`, or composes the grade isomorphism
with the entire-term conjugation isomorphism. Its conclusion is precisely
`CuspidalJacquetGradedPieces`, with the original actual root association.
No completeness, injectivity or distinctness condition on the supplied list of
representatives is needed by this implication: existence of the actual
zero-to-full filtration and all its grade isomorphisms is the substantive input.

`pointCuspidalJacquetFactor_of_geometricFiltration` applies the preceding
construction and `cuspidalJacquetFactor_of_finiteFiltration`. An irreducible
actual subquotient `tau` of `A` occurs in an actual grade by
`ObjectRepFiltration.exists_smoothGradedObject_subquotient`. Excluded grades
cannot contain it. A conjugate grade is irreducible when `sigma` is irreducible,
so actual subquotient occurrence identifies `tau` with that conjugate.
The returned rational point and dependent membership witness come from this
one grade and are unchanged throughout the construction.

The ambient object `A` and all grades are unrestricted smooth representations;
they have no finite-length, finite-generation or admissibility premise.
The filtration has finitely many steps and need not be a composition series.
Zero steps and empty simple-root sets are retained. The rational-point group
has its canonical `pointTopology`; local compactness, the nonarchimedean group
structure and closedness of the displayed Levi and radical families remain
visible. Universes `u` and `v` are independent, and carriers have universe
`max (u + 1) v`.

The proof is an internal composition of the named declarations, rather than a
separate literature assertion. The geometric comparison and vanishing inputs
have their existing structural hypotheses, while proper-target exclusion is
still assumed. The finite-filtration extraction uses actual invariant
subspaces, quotients, irreducibility and inverse conjugation
`x` maps to `sigma(n^-1*x*n)`. Its imported
`Classification.SupercuspidalSupport` declarations used for subquotient
presentation and isomorphism transport are elementary quotient algebra;
no classification conclusion is invoked. The subsingleton exclusion helper
in `SharpSupportRetentionReduction` likewise uses only an injective/surjective
subquotient presentation and irreducibility, not a support-retention theorem.
No geometric-lemma or adjointness theorem is invoked to establish these
conditional implications. A future use of such results to discharge the
displayed filtration and exclusion hypotheses must record their actual
declaration-level dependencies separately.
