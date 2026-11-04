# Adjoint translation coordinates and actual normalizer equivariance

For the supplied actual adjoint split-torus square
`IsAdjointSplitTorusImage q i j p`, `translationEquiv` chooses the linear
equivalence from the source KP translation space to the real cocharacter
space of the actual adjoint torus. The existing theorem
`adjointRealCocharacterComparison` supplies this equivalence. The formula
`translationEquiv_mk` says it is induced by the actual torus map `p`, and
`translationEquiv_unique` shows that this formula determines it uniquely.
The source translation space is the quotient by the common annihilator of
the actual relative roots.

The normalizer map is the actual point map constructed in
`GroupScheme.Adjoint.Normalizer`. Its torus square gives equivariance on
integral cocharacters by composition, hence on real cocharacters by tensor
induction. Quotient induction then gives
`translationEquiv_translationAction`: the source quotient derivative
intertwines with `normalizerAction j` of the actual image normalizer point.
Both actions are the Library's original actions on actual torus cocharacters.

For one supplied `D : KPApartmentData i ω`, `adjointDisplacement D x y`
expresses the torsor difference `x -ᵥ y` in these adjoint vector coordinates.
Its identities state additivity along three points, compatibility with
translation of the first point, and actual normalizer equivariance when both
points are acted on. The last identity uses the already constructed affine
normalizer action on this same `D`. No origin is chosen.

This is an internal construction and its intrinsic naturality laws from the
published adjoint comparison, the actual normalizer restriction, and the
original KP valuation-apartment torsor. No separate literature assertion is
formalized here. The hypotheses explicitly retain the needed affine and
monomorphism instances; the supplied image data imply them.
The target vector space is not an adjoint valuation apartment. This unit
does not construct such an apartment, an affine map between source and
adjoint apartments, full cross-torus A2, or a building.
