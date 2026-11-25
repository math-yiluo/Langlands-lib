# Finite generation of the actual nonnegative uniformizer quotient

`Langlands.GroupScheme.CocharacterUniformizer.coneQuotientFiniteGeneration`
proves `ConeQuotientFiniteGenerationStatement.{u}`. The result gives finite
generation of the actual submonoid `CAplusQuotient` at every instance of the
data in that published statement.

The proof equips the reductive group scheme with its affine and smooth
structure. Smoothness supplies local finite type. The maximal split torus
supplies splitness, so `IsSplitTorus.finite_simpleRelativeRoots` gives
finiteness of the actual set `R` of simple relative roots. The published
`cocharacterConeFiniteGeneration` then gives `AddSubmonoid.FG` for
`CocharacterCone.quotient T R`.

`AddMonoid.fg_iff_addSubmonoid_fg` and `AddMonoid.fg_iff_mul_fg` turn
this into `Monoid.FG` on the multiplicative version of the integral quotient
carrier. At the same data, `coneQuotientComparison` supplies a monoid
equivalence from that carrier to the carrier of the actual quotient submonoid.
The proof uses surjectivity of this map in `Monoid.fg_of_surjective` and applies
`Monoid.fg_iff_submonoid_fg` to obtain the required `Submonoid.FG`.

The [statement](CocharacterUniformizerConeFiniteGenerationStatement.md)
locates the common-uniformizer construction and ratio quotient in Renard
2026, V.2.5 and V.3.23–V.3.24. This proof gives the derived finite-generation
result by transporting generation of the integral quotient.
