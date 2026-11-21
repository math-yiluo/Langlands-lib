# Generic monodromy over a discrete valuation ring

`dvrGenericMonodromy_surjective` concerns the actual pointed finite étale
fundamental groups of the fraction-field spectrum and the DVR spectrum. The
base point on the DVR is the composite of the given geometric point with the
fraction-field map. The theorem gives surjectivity of `fundamentalGroupMap`
for this map, and `dvrGenericMonodromyLift` chooses a lift of each element.

The categorical and topological connectedness comparisons follow the
finite étale cover argument in `HarrisTaylorCMArtinianLevel`. Here the DVR
spectrum has integrally closed domain stalks. A connected finite étale cover
of it consequently has irreducible total space by
`EtaleNormalLocallyIrreducible.irreducibleSpace_of_etale`. It surjects onto
the DVR spectrum, so its pullback to the fraction-field spectrum is
nonempty. The fraction-field map is an open immersion and its base change
is therefore a nonempty open subscheme of that irreducible total space.
The resulting connected cover has a transitive action on its geometric
fibre. The actual pullback equivalence of geometric fibres transports this
action to the action through `fundamentalGroupMap`. Applying Mathlib's
surjectivity criterion for fibres of Galois objects gives the result.

This is a derived specialization of the Library's normal étale geometry,
finite étale fibre functor and functoriality, and Mathlib's Galois category
results. It supplies the monodromy surjectivity used to extend level orbits
over a given good model.
