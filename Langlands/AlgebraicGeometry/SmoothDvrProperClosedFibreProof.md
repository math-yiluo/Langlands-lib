# Properness of a smooth DVR family with proper closed fibre

`Langlands.AlgebraicGeometry.smoothDvrProperClosedFibre` proves
`Langlands.AlgebraicGeometry.SmoothDvrProperClosedFibreStatement`: a smooth,
separated, quasi-compact morphism `p : X ⟶ Spec V` over a discrete valuation
ring `V`, with geometrically connected fibres and proper pullback along
`Spec V/𝔪 ⟶ Spec V`, is proper.

A discrete valuation ring is a noetherian, integrally closed local domain.
The proof turns the four hypotheses on `p` into instances and applies
`Langlands.AlgebraicGeometry.isProper_of_smooth_of_proper_closedFibre` of the
module `Langlands.AlgebraicGeometry.SmoothLocalProperClosedFibre` to `p` and
the given properness of its residue-field pullback.

That criterion uses a proper surjective Chow modification of `X` which is
open in a proper envelope. The generic fibre of the envelope is geometrically
integral. Normality of the base then identifies the global functions of the
envelope with the base ring, so the envelope has a preconnected closed fibre.
The proper closed fibre of the modification fills that fibre, so the open
immersion is an isomorphism, and universal closedness descends along the
proper surjection to `X`. This proves the smooth DVR case of Grothendieck and
Dieudonné, *Éléments de géométrie algébrique IV*, third part (1966),
Corollary 15.7.10, printed p. 247.
