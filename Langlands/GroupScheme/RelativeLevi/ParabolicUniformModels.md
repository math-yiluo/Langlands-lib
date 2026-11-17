# Relative dynamic models for a uniform standard cocharacter family

This internal construction takes `UniformStandardCocharacterFamily` for an
actual coordinate split torus over a ring. For each fixed integer vector,
`parabolic` and `inclusion` give the actual affine dynamic subgroup scheme and
its map into the ambient group. The notation `AffineRegularBorel.cocharacter`
is used only for its general fixed-exponent construction; no regularity or
Borel claim is made for these models.

`relativeParabolic` applies `dynamicRelativeLevi` to the actual parabolic,
unipotent, and centralizer representatives, and hence proves that every model
is a relative parabolic whenever the ambient group is reductive.

`range_field` pulls back the representing inclusion and uses the fixed-exponent
cocharacter base-change identity. Thus the field pullback represents the dynamic
parabolic of the same integer vector on all scheme tests. `classifies_field`
uses fibrewise maximality to obtain a maximal split torus on the supplied field
algebra, and the family's fieldwise generic cocharacter and face equivalence.
It constructs the class index with `standardFamilyConjugacyIndex`; its
specification and uniqueness theorems prove the exact all-test conjugacy claim.
These constructions derive solely from the published dynamic and field
classification results and do not assume a relative parabolic moduli scheme.
