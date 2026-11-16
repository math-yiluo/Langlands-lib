# Finite coefficient descent of the three quasi-finite model properties

This internal auxiliary module specializes published scheme limit descent
theorems to a supplied group homomorphism between already defined models.
`quasiFiniteFlatSurjectiveProperty` is the conjunction of local quasi-finiteness,
flatness, and surjectivity of the actual scheme map. It imposes no finiteness
condition.

The structural descent theorem uses relative flatness descent and relative
pure fibre dimension descent at dimension zero. The latter agrees with local
quasi-finiteness for locally finite type maps, including empty fibres.
Both source and target structural maps are locally finitely presented,
quasi-compact and quasi-separated; these hypotheses give the needed finiteness
properties of the relative map. Surjectivity uses the published descent theorem
for the constructible nonempty fibre locus.

Each property is detected at a stage of the affine inverse limit.
Cofilteredness gives a common incoming stage, and cartesian naturality squares
preserve the properties there. Conversely, the cartesian cone square transports
all three properties to the limit.

`exists_fg_hom_property` applies structural descent to the directed system of all
finitely generated subalgebras of an arbitrary coefficient algebra. The
published spectrum cone is a limit, since those subalgebras cover the algebra.
The canonical arrow isomorphism exchanging the two pullback factors identifies
the scheme limit convention with the actual group base change convention.
The resulting stage is a finitely generated coefficient subalgebra, with the
specified group homomorphism after base change. Its specialization
`exists_fg_hom_quasiFinite_flat_surjective` retains the three properties
simultaneously.

The provenance is the Library's `relativeFlatDescent`,
`relativePureFibreDimensionDescent`,
`hasPureDimensionFibers_zero_iff_locallyQuasiFinite`,
`surjective_schemeStructuralPropertyDescent`, and
`nonempty_isLimit_specCone`. This module supplies their internal coefficient
specialization, with no additional original-literature claim.
