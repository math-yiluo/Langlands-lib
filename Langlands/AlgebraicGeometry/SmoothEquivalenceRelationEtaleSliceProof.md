# Etale slices of smooth equivalence relations

The theorem `Langlands.AlgebraicGeometry.smoothEquivalenceRelationEtaleSlice`
proves the published proposition
`SmoothEquivalenceRelationEtaleSliceStatement.{u}` for every universe `u`,
with exactly its hypotheses. For schemes `U` and `R` and an absolute
equivalence relation `t,s : R → U` with smooth projections, it gives a scheme
`V` in the same universe and a locally finite type morphism `g : V → U`
such that `pullback.snd g t ≫ s` is etale and surjective.

The statement and the equivalence-relation condition are imported unchanged.
The proof uses Mathlib's scheme morphism properties and pullback. It is a
direct composition of the good-point existence, local slicing, image
saturation and globalization results named below.

## Implemented proof

The auxiliary theorem
`exists_etale_surjective_slice_of_goodPoint_orbits` assumes a common section
`e : U → R`, with `e ≫ t = 𝟙 U` and `e ≫ s = 𝟙 U`, and the orbit condition
that for each `x : U` there is `r : R` such that `s r = x` and `t r` satisfies
`SmoothRelationGoodPoint.IsGoodPoint t s e`. It also assumes the published
equivalence-relation condition and smoothness of `s`.

For a supplied good point `y`, the imported theorem
`exists_etale_slice_of_isGoodPoint` from `GoodPointEtaleSliceProof` provides a
locally finitely presented morphism `g` with etale associated relation map
and a point of its domain above `y`. Local finite presentation implies local
finite type. These data are the local-slice hypothesis of
`exists_etale_surjective_slice_of_orbit_slices` from
`RelationEtaleSliceOfOrbits`.

That imported globalization result uses reflexivity to put `t r` in the
associated slice image and forward image saturation to put `s r = x` in
the same image. It then takes a coproduct of local slices indexed by finite
type points of `U`. Source locality gives local finite type and etaleness,
and openness of the etale image together with the finite type point test
gives surjectivity. The resulting scheme remains in `Scheme.{u}`.

The final theorem introduces exactly the hypotheses of the published
statement. Applying `hr.refl U (𝟙 U)` gives the common section `e` and its
two identities. The imported theorem
`SmoothRelationGoodPoint.exists_isGoodPoint`, from
`SmoothRelationGoodPointExistence`, uses `hr.mono`, smoothness of `s` and
these identities to prove the orbit condition for every point of `U`.
The auxiliary theorem now supplies the required slice. The smoothness
hypothesis on `t` is retained in the exact target; the implemented
composition only needs smoothness of `s`.

## Provenance and inputs

This is an internal assembly of proved constructions. Good-point existence
uses differential generation from monicity, etale coordinates, a prime in
an open set with simple integer polynomial equations, and the affine-chart
criterion for goodness. Local slicing uses the differential slice and
good-point cotangent constructions followed by propagation and open
shrinking. Each imported module's Markdown describes its proof and scope.
No quotient existence or unproved Library proposition is assumed.

Workers 101, 303 and 424 contributed to the good-point, local-slice and
globalization development and the final assembly.
