# Scheme restrictions on the reduced actual torsion closure

This module constructs the ideal sheaf, reduced closed subscheme, and closed immersion associated with the Zariski closure of the actual two-power torsion locus. It proves `TwoPowerTorsionReducedClosureStatement` over any field.

Reducedness reuses the published `IntegralSubscheme.isReduced_vanishingIdeal`
from the attributed Anthropic-FLT module
`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal`.
That theorem checks the standard affine cover: each affine coordinate ring is the quotient by a vanishing ideal, which is radical. The closed immersion has exactly the desired point image by the support computation for a vanishing ideal sheaf. A map from a reduced scheme whose image is contained in the closed set factors through this subscheme: pushforward of the zero ideal is the morphism kernel, while pushforward of a vanishing ideal is the vanishing ideal of the closure of its image. This factors the unit section.

An ambient scheme automorphism preserving the closed set induces maps on the subscheme in both directions using `IdealSheafData.subschemeMap`. The composite identities follow by cancelling the closed immersion. Inversion preserves the actual torsion locus and its closure. The preceding section-subgroup proof supplies the image equality for every rational translation in the closure. Applying this restriction construction gives the required automorphisms and their commuting equations.

The provenance is the internal reduced-scheme part of the closure argument motivated by Edixhoven, van der Geer and Moonen, *Abelian Varieties*, Chapter V, §3, Theorem (5.30), printed page 84 / PDF page 88. This construction does not establish a multiplication on the reduced subscheme, a subgroup scheme, a numerical rank, or density.
