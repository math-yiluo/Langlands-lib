# Reductivity of descended normal quotients

This auxiliary module, derived from existing Library results, proves
`Langlands.GroupScheme.ReductiveNormalQuotientEtaleGluingStatement` in every
universe. Let `G` be smooth and affine over an arbitrary scheme `S`, and let
`i : N → G` be monomorphic on the underlying schemes over `S`. Assume that
`N` is smooth and its all-test range is normal. If every point of `S` lies in
the image of an étale neighbourhood on which the pullback of `G` has a
reductive fppf quotient by the pullback of `N`, then there is a reductive
group scheme `M` over `S` and an actual fppf quotient `G → M` by precisely
the range of `i`.

The quotient retains flatness, scheme-surjectivity, local finite presentation
and equality of its full kernel range on all scheme tests. There is no
affineness, quasi-compactness, noetherian or field hypothesis on `S`.
Local reductive quotient schemes are supplied data.

## Implemented proof

`IsReductive.of_iso` transports smoothness and affineness through the
underlying scheme isomorphism and transports the geometric-fibre predicate
through its actual pullback.

`IsReductive.of_pointwise_baseChange` concerns a smooth affine group.
It assumes reductivity after base changes whose images jointly contain all
points of the base; these base maps need not be étale. At a point `s`,
choose a point `t` above it on one of those bases. The residue-field fibre
at `t` is connected reductive. Pullback-composition coherence identifies it
with the pullback of the original group to the corresponding field-valued
point of `S`. The canonical residue-field embedding factors this point
through the residue-field fibre at `s`. Reflection of connected reductivity
along arbitrary field extensions therefore proves reductivity of that
residue-field fibre. Extension to its algebraic closure and pullback
coherence supply exactly the geometric-fibre predicate in `IsReductive`.
Smoothness and affineness remain explicit hypotheses of this helper.

`RelativeRoot.IsFppfQuotient.smooth_target_of_smooth_represented_kernel` treats an affine quotient of a
smooth affine group by a smooth monomorphic subgroup. Affineness gives
quasi-compactness of the quotient map. The represented-kernel smoothness
theorem makes that map smooth, and smoothness descends from the source
along the smooth surjective projection.

`NormalQuotient.isReductive_of_pointwise_quotients` applies this smoothness
result to a supplied affine quotient `M`. After each pointwise base change,
the quotient map to the pullback of `M` and the supplied reductive quotient
have exactly the same all-test kernel. Both maps are quasi-compact, since
their sources and targets are affine over the common base. The published
common-kernel comparison gives an actual group scheme isomorphism between
the targets, so the pullback of `M` is reductive. The pointwise reflection
helper then proves reductivity of `M` itself.

Finally, `exists_reductive_fppfQuotient_of_pointwise_etale` first applies
affine normal quotient gluing, forgetting only reductivity in its local
inputs. The preceding comparison result proves reductivity of the
resulting affine quotient.

## Provenance and scope

This is an internal consequence of affine normal quotient gluing,
common-kernel comparison, smooth represented-kernel quotients, descent of
smoothness, and preservation and reflection of connected reductivity under
field extension. It introduces no external-source assertion.

This module does not construct local dynamic presentations or identify the
unipotent radical of a relative parabolic with its contracting subgroup.
It does not prove annihilation or the universal property in the original
relative parabolic reductive quotient target. These are not part of this
module; that target, `RelativeParabolicReductiveQuotientStatement`, is proved
as `relativeParabolicReductiveQuotient` in `RelativeLevi.ReductiveQuotientProof`.
