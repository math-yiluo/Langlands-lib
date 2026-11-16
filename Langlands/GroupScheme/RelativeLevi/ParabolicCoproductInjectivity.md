# Injectivity for disjoint coproduct parabolic charts

This is an internal criterion for the actual coproduct chart. For a reductive
group scheme `G` over an arbitrary scheme `S`, take a family of `S`-schemes `V i`
and actual parabolic families `F i` on them. The hypotheses require injectivity
of each component's family on every test scheme, and require equality between
values of two component families to imply equality of the indices or emptiness
of the test scheme. The index type lies in the scheme universe; no finiteness
hypothesis is needed.

`eq_sigmaOverι_of_restrict_eq` proves equality of two parameter morphisms after
their respective component inclusions when the component-family values agree.
For equal indices it uses component injectivity; on an empty source it uses
uniqueness of scheme morphisms.

`coproductParabolicChart_injective_of_disjoint` treats arbitrary parameter maps
into the scheme coproduct. It pulls back the component cover along the first map,
then refines each component by the cover pulled back along the second map.
On each refinement both maps factor through components. Restricting the assumed
equality of family values and using the coproduct family's component equations
allows application of the preceding result. Equality on the two successive open
covers proves equality of the original scheme maps.

`coproductParabolicChart_mono_of_disjoint` converts the resulting injectivity
on all test schemes to monicity of the natural transformation. No type
disjointness or coverage theorem is assumed implicitly or proved here. The
companion finite quotient chart applies this criterion to the actual finite
coproduct of smooth proper quotient schemes.
