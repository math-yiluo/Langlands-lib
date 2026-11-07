# Actual source-radical and stabilizer coefficient quotients

This internal adapter compares two actual quotient modules, naturally in
every smooth complex representation `A` of the original source Levi's
rational points. The group and coefficient universes are independent.
All point groups carry the original canonical or represented Levi topology.

Write `H = Q ∩ z⁻¹Pz` for the full orbit stabilizer in the original target
parabolic's point image, `πQ` for that parabolic's actual Levi projection,
and `NQH = πQ.ker.comap H.subtype`. Let `fH` be the original
`stabilizerToLeviPoints`, and let `R = pointImage (D.r' ≫ D.p')` be the
source intersection radical in the original source Levi's own points.
The coefficient on `H` is the original inducing positive-half twist of `A`,
pulled back through `fH`, as in `stabilizerTwistedCoefficientFunctor`.

`sourceRadicalQuotientToStabilizerCoinvariants` is an unconditional linear
surjection from the actual trivial-character localization quotient
of `A` by `R` to that coefficient's actual `NQH`-coinvariants.
It keeps the class of every original vector. To verify each relation,
the proof uses the canonical inverse-conjugation radical lift from
`RepresentedGeometricLemmaRadicalLift`. The original source Levi projection
recovers the same radical point. The original inducing half-character
is trivial on `R` by
`sourceRadical_le_ker_inducingHalfCharacter`, so the lifted coefficient
relation is precisely the source-radical relation. The map is onto
because every target quotient class has an original vector representative.
Its naturality equation commutes with every morphism of the original
smooth coefficient objects.

The reverse map and `stabilizerCoinvariantsSourceEquiv` require the explicit
intermediate geometric inclusion
`Subgroup.map fH NQH ≤ R`. The canonical lift already supplies the opposite
inclusion, so this input is the missing direction of an actual subgroup
image equality. For a point of `NQH`, the input places its image in `R`.
The same half-character triviality and the actual localization relation
then make the identity on original vectors descend in the reverse
direction. The two descended maps are inverse because both composites
keep every original vector class. The equivalence is natural for every
coefficient morphism.

The provenance is the original intersection datum, its literal-point
radical lift and source-projection section identity, the internally proved
half-character triviality, and the universal properties of the two actual
quotients. This module does not discharge the reverse image inclusion,
identify residual group actions, or prove the distinct-radical modulus
balance or the closed normalized orbit comparison.
