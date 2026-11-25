# Split projection of the regular dynamic Borel

This is an internal construction from the published dynamic subgroup,
centralizer and fppf quotient theorems. Its source motivation is Conrad,
*Reductive group schemes* (2014), Theorem 5.1.13, pp.143–145, and the proof
of Corollary 5.2.13(1), pp.158–159. The implementation uses the Library's
actual dynamic representatives and their all-test universal properties.

Over any commutative ring, `AffineRegularBorel.contractingGroup i n` is the
constructed affine group representing the contracting subgroup for the
cocharacter with coordinate exponents `n`. `contractingInclusion` factors
its original ambient inclusion through the dynamic parabolic. Its composite
is the original inclusion, so closedness and affineness follow from the
published closed subgroup constructions.

Suppose the ambient group is reductive, `i` is a closed fibrewise maximal
coordinate split torus, `P` is its fibrewise root datum, and `n` pairs
nontrivially with every root. The published arbitrary-base centralizer
comparison makes `i` itself an all-test representative of the cocharacter
centralizer. `torusSection` is the resulting centralizer inclusion into the
parabolic; `torusProjection` is limit at zero with values in this original
torus. The section followed by the ambient Borel inclusion equals `i`, and
the section followed by the projection is the identity.

Smoothness of the contracting representative, together with the published
`Dynamic.isFppfQuotient_limitGroupHom_range`, proves that this projection is
flat, surjective and locally of finite presentation. Its actual scheme
kernel has the same subgroup functor as `contractingInclusion` on every test
scheme. Thus the construction includes actual group schemes, morphisms,
and kernel equality; it does not rely only on fibrewise existence.

Finally `hasSplitBorelVectorSeries_of_contractingSeries` assembles these
constructions and the published relative-Borel theorem. It assumes a finite
`HasAffineVectorSeries` for this specific contracting group and concludes
`HasSplitBorelVectorSeries i`. It does not construct that series or prove
`SplitBorelVectorSeriesStatement`. No connectedness, reducedness, localness,
nonzero-ring, or field hypothesis is imposed.
