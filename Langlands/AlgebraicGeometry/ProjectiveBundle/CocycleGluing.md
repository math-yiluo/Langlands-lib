# Gluing relative projective schemes by coordinate cocycles

Fix a locally directed open cover `𝒰` of a scheme `S` and a natural
number `n`. For each arrow `i ⟶ j` between cover indices, a
`CoordinateCocycle n 𝒰` specifies an invertible coordinate linear map
over `Γ(𝒰.X i, ⊤)`. Its identity condition gives the identity coordinate
map. Its composition condition first applies the coordinate map from
`i` to `j`, then the map from `j` to `k` with all coefficients pulled
back to `i`. This is a strict general-linear cocycle.

The construction `chartFunctor` associates the actual relative
projective scheme over `𝒰.X i` to each index. Its arrow map first acts
by the specified coordinate automorphism, then uses the canonical
change-of-base morphism. Naturality of global coordinate actions and
the cocycle condition prove functoriality. The resulting squares over
the cover's transition morphisms are Cartesian: each is the canonical
relative projective base-change square with an automorphism inserted
in its upper-left corner.

If the cover's index category is thin and small in the scheme
universe, `CoordinateCocycle.scheme` is the actual glued scheme.
It has a structure morphism to `S` and an open immersion from each
specified projective chart. These charts cover it. The chart
inclusions satisfy exactly the specified coordinate transitions.
Each chart is the inverse image of its corresponding member of the
base cover, as an actual Cartesian square of schemes.

This is derived internal infrastructure. The chart maps use the
previously constructed actual actions on relative projective space.
The Cartesian-square argument transports the existing
`RelativeProjectiveSpace.isPullback_map` through the coordinate
automorphism. Mathlib's `Scheme.Cover.RelativeGluingData` then
constructs the scheme as a colimit, and supplies the open chart cover,
structure morphism and local Cartesian property. No new external
source assertion is used.

The cocycle is explicit input here. Constructing it from local frames
of a locally free sheaf, comparing frame choices, gluing the
tautological invertible sheaf and constructing the abelian moduli
scheme are further obligations.
