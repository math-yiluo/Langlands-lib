# Right translation in nonnegative rectangular integrals

This internal construction uses the actual adelic general linear groups,
the published rectangular chart and its normalized additive Haar measure.
For every number field `F : Type u`, ranks `t < r`, leading blocks `g,a`
of rank `t+1`, and rectangular matrix `x`, block multiplication gives
`rect(g,x) pad(a) = rect(g a,x a)`. The proof uses consecutive block
coordinates and the published identification of padding with reindexed
rank inclusions, reusing `Unfolding.rankInclusion_eq_lowerBlockPair`
from `DualExpansionFinal`.

`rectangularRightIntegral` integrates an arbitrary extended nonnegative
function at `rect(1,x) pad(g)`. Under compactness of the additive adelic
quotient, a measurable input has this value equal to its integral at
`rect(g,x)`, multiplied by `ofReal(|det g|^(-k))`, where
`k = r-(t+1)`. The inverse power here is the inverse of the natural
power `|det g|^k`.

The implemented change of variables is the Library's proved
`rectangleMeasureModulus`: pushing rectangular Haar forward by `x ↦ x g`
scales the measure by this same inverse determinant factor. The
lower-integral pushforward and scalar-measure identities apply to
measurable extended nonnegative functions, including those whose
integrals are infinite. The code first proves this general
`lintegral_rectangle_mul_right` formula, then applies the block identity.

The same formula with an arbitrary leading block describes right
translation of that block under rectangular integration. As a
consequence, if right multiplication by `pad(a)` preserves the original
function and `|det a|=1`, then right multiplication by `a` preserves its
rectangular integral. These two hypotheses are explicit; this module
does not assert that padding preserves a chosen compact subgroup.

The construction is derived from published block geometry and the
published rectangular Haar modulus theorem, with no new analytic
convergence input. It preserves all ranks, including the zero-row
rectangle. Finiteness and a uniform Mellin half-plane remain separate
obligations.
