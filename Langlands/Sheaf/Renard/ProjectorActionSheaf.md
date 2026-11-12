# Compatible actions on Renard's original complex projector sheaf

This construction implements the reconstruction direction of Renard III.3.1,
printed p.83 / PDF p.89, using the projector sheaf of II.2.5, printed pp.39–40 /
PDF pp.45–46. Source: David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The opening definition of III.3.1 identifies action sheaves with
nondegenerate pointwise test modules carrying compatible linear actions.
The formulas here are an internal implementation of the reconstruction
implicit in that identification, on the published II.2.5 vector sheaf.
They construct the functor and its intrinsic laws, without asserting the
sheaf/module equivalence.

All declarations have prefix
`Langlands.Sheaf.Renard.ProjectorActionSheaf`.

## Original objects and hypotheses

The source is the existing category
`CompatibleTestActions.CompatibleTestAction.{uG,0,0} G X`. Its module is an
original nondegenerate module over
`PointwiseTestAlgebra.Carrier X`, with the published canonical complex
structure, an original complex-linear representation, and the literal
compatibility law with inverse pullback on tests.

The space and module carriers are in `Type`; complex coefficients and the
group's independent universe are retained. The explicit hypothesis
`hX : IsLocallyProfinite X` is Hausdorffness together with a compact-open
neighbourhood basis. `ContinuousConstSMul G X` says that each actual base
translation is continuous; its inverse is another such translation. This
construction needs no topology on `G`, no smoothness, no transitivity and
no sigma-compactness. Renard's jointly continuous action of a t.d. group
is a specialization. These weaker hypotheses concern construction data,
not a generalization of an asserted equivalence theorem.

The section spaces are exactly
`ProjectorVectorSheaf.familySpace hX M.module.property U`: the published
compatible families of the original compact-open projector ranges
`Value hX M.module.obj W`. Their scalar structures, restrictions and
ordinary sheaf condition are reused by Lean name. No sheafification,
replacement module carrier or replacement sheaf carrier is introduced.

## Transport on the compact-open ranges

`translateCompact g W` is the compact-open object whose underlying open is
`ActionOpens.translate g` of the original `W`. Its points satisfy
`g⁻¹ • x ∈ W`. Compactness follows by identifying this set with the image
of `W` under `g`. `translateCompact_one`, `translateCompact_mul` and
`translateCompact_mono` give the actual identity, multiplication and
inclusion laws on these compact-open objects.

`test_translate` and `test_inverse_translate` are literal inverse-pullback
formulas for the existing characteristic test functions. The first says
`g · χ_W = χ_(g W)`, and the second says `g⁻¹ · χ_(g W) = χ_W`.
Both are checked pointwise on the original test algebra.

`valuePull g W` applies `M.action g⁻¹` to an original vector in the projector
range at `g W`. The given compatibility law and the second characteristic
formula prove that its image is fixed by `χ_W`, so it lies in the original
range at `W`. `valuePull_restrict` is the same covariance law applied to a
smaller projector. `valuePullLinear` uses the original complex linearity of
the group operator and the published canonical scalars on both ranges.
These maps impose no extra action hypothesis beyond the existing
compatible-action data.

## Transport on the published family spaces

For an actual transport-category arrow `f : U → V` labelled by `g`,
`translatedInside f` sends a compact open `W` inside `U` to `g W` inside
`V`; the arrow's original `mapsTo` field proves the inclusion.
`familyPull f` sends a published compatible family `s` over `V` to the
family over `U` whose original-module component is

```text
(familyPull f s)_W = M.action g⁻¹ (s_(g W)).
```

`familyPull_val` is this literal formula. The resulting family is
compatible because `valuePull_restrict` commutes with the original
projector restrictions and `s` satisfies the original family compatibility
condition. `familyPullLinear` is this same map with complex linearity
proved componentwise. The inverse label is the convention of the existing
transport category; labels are retained even if the base action is not
faithful.

`translatedInside_id` and `translatedInside_comp` identify the actual
component indices. `familyPull_id` and `familyPull_comp` then use the
original representation's identity and multiplication laws, including
reversal under inversion. `transportPresheaf` bundles these spaces and
maps as a functor on the original transport category.

## The actual sheaf and its functor

`familyPull_inclusion` proves that label-one arrows give exactly the
published ordinary restrictions, discarding components outside the smaller
open. `underlyingIso` is therefore an isomorphism with the published
`ProjectorVectorSheaf.presheaf`, with identity maps on all family spaces.
`isSheaf` transports the existing ordinary sheaf condition through this
isomorphism. `sheaf hX M` is the resulting object of the existing
`SectionActions.ActionSheaf G X`, and `underlyingSheafIso` is its
identity-on-families ordinary vector-sheaf comparison.

For a morphism of compatible actions, `transportMap` uses precisely
`ProjectorVectorSheaf.presheafMap` on every open. Its labelled naturality
is the given commutation equation between the original module map and the
original group operators, applied componentwise. `sheafMap` bundles this
as the existing equivariant sheaf morphism. `functor hX` is the actual
reconstruction functor on every compatible object and map; identities and
composition follow componentwise from the original module maps.

`forgetIso` is the natural comparison between forgetting the reconstructed
group action and applying the published vector-sheaf functor to the
original underlying test module. Its components are `underlyingSheafIso`;
naturality retains the same original componentwise module maps.

No module-to-compact-section comparison is assumed. Smoothness of this
action sheaf, the equivariant canonical comparison maps and the
sheaf/module equivalence remain separate obligations, as do the induction
sheaf, the coinvariant sheaf and their III.3 assertions.
