# Fixed-family standardization of specified parabolic and Levi maps

`parabolicLeviStandardConjugatingPoint` is an internal composition of the
simultaneous dynamic-realization and fixed-family conjugation constructions.
It fixes a connected reductive group scheme `G` over an arbitrary field `k`,
a maximal split torus map `i`, a generic cocharacter `ν`, an actual
parabolic map `p : P ⟶ G` and a rational Levi map `l : M ⟶ P`.

The explicit structural inputs are `ParabolicDynamicStatement`,
`DynamicGeometricUnipotentRadicalStatement`,
`SmoothMaximalSplitTorusConjugacyStatement` and `HasRelativeRootSystem i`.
None is proved by this module. Connected reductivity supplies affineness,
smoothness and connectedness for the imported constructions; maximality
supplies the monomorphism used by the actual root-system premise.

The dynamic-realization construction chooses a single actual ambient
cocharacter and proves that its dynamic parabolic and centralizer are the
all-test images of the supplied `p` and `l ≫ p`. The standard-conjugation
construction then chooses one rational point `g`, retaining existential
`J` and `ζ`. Its subtype certificate gives `IsStandardCocharacter i ν J ζ`
and all four equalities: the two images postcomposed with `Int(g)` equal
the fixed family's `standardParabolic` and `standardLevi`, and equal the
dynamic parabolic and centralizer of this same `ζ`.

The original source objects, maps and fixed torus/chamber remain unchanged.
The result concerns subgroup functors on every test scheme, in arbitrary
characteristic and without splitness or positive-rank assumptions. It is a
conditional geometry adapter, with no representation or topology input and
no new source translation. The remaining structural proofs and the separate
normalized/raw logarithmic source comparison are not discharged here.
