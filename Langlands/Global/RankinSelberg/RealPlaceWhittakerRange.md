# The specified Whittaker model at a real place

For any real place with supplied cuspidal parameter and any component of a
unitary adelic additive character trivial on the ground field,
`realPlaceWhittakerRange` realizes each member of the corresponding local
Whittaker model as the restriction of a cuspidal Whittaker function with
finite coordinate one. `realWhittakerRestrictionOnto` applies this result
also to the inverse additive character, whose real scale is \(-a\).

To compare local coefficient maps, the proof pulls the normalized map
and an arbitrary map back through the same surjective compact-finite
intertwiner from the ascending real character principal series.
`RealExactStandardEvaluation.exists_standardEvaluation` supplies continuous
smooth evaluations of the two pullbacks. The corresponding linear forms on
the smooth position principal series have the same Whittaker covariance and
finite compact derivative bounds. A lift of the vector of identity value one
shows the first form is nonzero, so the principal-series uniqueness theorem
makes the second a scalar multiple of the first. Surjectivity of the
intertwiner puts the value of the original map in the range of the normalized
map. That range consequently contains the sum of all coefficient ranges,
which defines the specified real Whittaker model.

The global construction uses `archimedeanActualWhittakerIntertwiners` for
the normalized map and then chooses its preimage vector. This is a derived
comparison of the Library's actual restrictions with the real Whittaker
models used in H. Jacquet, *Archimedean Rankin–Selberg Integrals* (2009),
§2, author-posted pp. 3–4.
