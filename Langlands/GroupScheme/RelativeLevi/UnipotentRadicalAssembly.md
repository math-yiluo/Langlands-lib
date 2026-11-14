# Relative radical data with uniqueness from pointwise dynamic presentations

`radicalWithUniquenessOfPointwiseDynamic` is an internal assembly of the local
construction and global comparison interfaces. Its inputs are a reductive group
scheme `G`, an affine group scheme `P`, a homomorphism `iP : P ⟶ G`,
`DynamicRelativeLeviStatement`, and a pointwise etale dynamic presentation of
the actual pullback of `iP`. The base and universe are arbitrary.

For each base point, the presentation hypothesis supplies an etale neighbourhood
containing that point and a cocharacter whose dynamic parabolic is represented
on all tests by the pullback of `iP`. `etaleDynamicCoverOfPointwise` chooses these
neighbourhoods as one actual etale cover. `radicalOfEtaleDynamicCover` constructs
and glues local dynamic radicals along this cover, giving a global group scheme
`U`, an inclusion `r : U ⟶ P`, and the full `IsRelativeUnipotentRadical r`
certificate.

The same cover is then used by `radical_range_eq_of_etale_dynamicCover` to show
that every other inclusion with the full relative radical certificate has the
same subgroup functor range as `r`. Thus the output contains actual radical
data together with uniqueness on every relative test scheme, including
nonreduced tests.

The provenance is internal composition of the named constructions and comparison
theorem. The pointwise presentations and dynamic relative Levi theorem remain
explicit inputs; this module does not prove the unconditional
`RelativeUnipotentRadicalStatement`.
