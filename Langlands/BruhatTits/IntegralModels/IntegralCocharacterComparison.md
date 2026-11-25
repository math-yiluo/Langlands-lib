# Integral cocharacters under a change of coefficients

This internal supporting result compares actual integral cocharacters over a
coefficient square of integral domains and their fraction fields. The downstairs
torus has a specified generic fibre and inclusion in the neutral integral model.
The upstairs split integral torus has a generic inclusion factoring the base
change of the downstairs generic inclusion. Every downstairs integral
cocharacter, composed with the downstairs inclusion, pulls back to exactly the
ambient integral cocharacter obtained from the upstairs split torus and that
generic factorization.

The proof uses the published normalized cocharacter tower identity twice to
compare the two paths around a commuting pullback square. It computes the
generic fibre of the downstairs ambient cocharacter using the given torus
square and the published model coefficient comparison. The upstairs ambient
cocharacter has the same generic fibre by its published construction. A flat
source and separated target determine a morphism from its generic fibre;
the multiplicative group is flat and the integral model is affine. This gives
literal equality of the two integral group-scheme homomorphisms.

The result is derived from the Library's pullback comparisons, split-torus
cocharacter equivalence and generic-fibre rigidity. It makes no additional
original-literature translation claim. It supplies a comparison needed for
descended facet parabolic images, without asserting the full facet order
bijection.

All schemes and rings are at arbitrary universe `u`. The coefficient square
consists of integral domains `R`, `A`, their fraction fields `K`, `L`, the
algebra maps `R → A → L` and `R → K → L`, and their scalar-tower
compatibilities. The neutral model comes from supplied relative-component
model data `D`. The downstairs integral torus `T` has specified generic
identification with `S` and generic inclusion `i`. The upstairs integral
split torus `T'` belongs to the coefficient base change of this neutral model.
The supplied homomorphism `f` from the base change of `S` to the upstairs
generic torus satisfies `f ≫ i' = baseChange(i)`. No existence assertion
for `T`, `T'`, or `f` is part of this result.

For the residue conclusions, `R` and `A` are local and `R → A` is a local
homomorphism. The canonical map between their residue fields determines the
actual special-fibre coefficient square. The theorem
`IntegralTorusData.baseChange_specializedAmbientCocharacter` reduces the
integral equality around this square. If `T` is split,
`IntegralTorusData.coefficientCompatibleSpecialization` proves the named
Prop-valued definition
`IntegralTorusData.HasCoefficientCompatibleSpecialization`: for every
generic cocharacter `c` of `S`, residue base change of its canonical
downstairs specialization, composed with the special-fibre square
isomorphism, equals the upstairs specialization of `baseChange(c) ≫ f`
as an ambient group-scheme homomorphism.

The proof writes `c` as the generic fibre of an integral cocharacter using
the downstairs split-torus cocharacter equivalence. Its inverse cancels in
canonical specialization. Applying the normalized cocharacter tower
identity to the residue square then reduces the assertion to the already
proved equality of integral homomorphisms.

For any supplied special-fibre quotient data `Q`,
`IntegralTorusData.baseChange_quotientCocharacter` composes this equality
with the actual base-changed quotient projection. The square isomorphism
and its inverse cancel. Thus the two resulting quotient cocharacters agree
literally. The theorem `IntegralTorusData.baseChange_quotientParabolic`
applies the published dynamic-parabolic base-change theorem: the dynamic
parabolic of the upstairs quotient cocharacter is the residue-field base
change of the downstairs dynamic parabolic. These are equalities of
subgroup functors on all scheme tests.

This module compares canonical constructions for supplied torus data. It does
not prove arbitrary parabolic attainment, facet-model existence, or the
facet order bijection `UnramifiedFacetParabolicOrderStatement`.
