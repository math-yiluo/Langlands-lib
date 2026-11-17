# Simultaneous finite étale local splitting

This derived reduction constructs one local finite étale extension of a
complete local noetherian base over which the source group is diagonalizable
and the actual special fibre of the target group is diagonalizable. It
requires neither flatness nor finite type of either group for this reduction.
It does not show that the target group itself is diagonalizable.

`LocalSplittingData A H` consists of a local finite étale `A`-algebra `B`, a
local structural map, and a proof that `H_B` is diagonalizable in the relative
sense, including finite generation of its character group. Its `residueData`
uses the canonical residue-field quotient to apply the interfaces of
`ResidueExtensionData`. Consequently `B` is finite free and faithfully flat
over `A`, its spectrum is a finite étale surjective cover, and it is complete
and noetherian whenever `A` is complete and noetherian.

`localSplitting A H hH` assumes a Henselian local base and the given finite
étale surjective splitting cover of `H`. Its covering scheme is affine because
it is finite over an affine scheme. Replace it by the spectrum of its global
sections and choose a point above the closed point of the base. The published
`henselianFiniteEtaleRefinement` provides a factorization through a local
finite étale `A`-algebra. Pulling the supplied diagonalizable presentation
back along this factorization, and comparing successive base changes, proves
the splitting assertion. Finite flat modules over local rings are free; a
nontrivial free algebra has faithful scalar action. Integrality then reflects
units and proves that the structural map is local.

`henselianLocalRing_of_complete` derives the local-ring convention for
Henselianity from the published `IsAdicComplete.henselianRing` instance. A
unit derivative maps to a unit in the residue field, so its Hensel lifting
property applies directly.

`specialFibreBaseChangeIso` is the actual comparison between the special
fibre of `G_B` and the base change of `G_k` to the residue field of `B`, for
any local algebra map `A → B`. It composes the two successive-base-change
comparisons and the commutative square of residue-field maps.

`SimultaneousSplittingData A G H` contains `LocalSplittingData A H` and a
proof that the actual special fibre of `G` after that same base change is
diagonalizable. The constructor `simultaneousSplitting A G H hH hG` assumes
that `A` is complete local noetherian, that `H` has a finite étale surjective
splitting cover, and that the special fibre of `G` is of multiplicative type.
First apply `localSplitting` to obtain `B`. The special-fibre comparison and
base-change stability preserve the multiplicative-type hypothesis for
`G_B`. Apply `specialFibreSplitting` to obtain a further local finite étale
extension `C/B` that splits this special fibre. Compose the two extensions.
Their finite and étale properties are stable under composition, and locality
is preserved by composition. The source remains diagonalizable after the
second extension. Pulling the comparison between `G_C` and `(G_B)_C` to the
actual residue field identifies the final target special fibre with the
one already proved diagonalizable.

This is internal content derived from the published Henselian finite étale
refinement theorem and the field-splitting construction in
`CompleteLocalSplittingExtension`. It supplies the simultaneous splitting
reduction in the proof of Conrad (2014), Theorem B.3.2(2), pp.288–289. It
asserts no diagonalizable deformation theorem, adic-effectivity theorem,
unique Hom lifting theorem, or open-and-closed immersion theorem.
