# Compact sections with compatible group and test actions in Renard III.3.1

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, III.3.1 Definition, printed p.83 / PDF p.89,
especially the identification with nondegenerate `D(X)`-modules carrying a
compatible linear action. It is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The module constructs the forward functor in that identification using the
published ordinary compact-section functor from Renard II.2.5. It does not
assert an equivalence or construct its inverse.

All declarations have prefix
`Langlands.Sheaf.Renard.CompactSectionActions`.

## Hypotheses and original objects

The group `G : Type uG` has a topology and acts jointly continuously on
`X : Type`. The explicit predicate `hX : IsLocallyProfinite X` means
Hausdorff with a compact-open neighbourhood basis, retaining Renard's t.d.
space convention. The coefficient field and section carriers are the
original universe-zero complex vector spaces, as required by the existing
`CompactSupport` and `CompactSectionTestModule` interfaces. The group
universe is independent. These constructions require no smoothness of
individual action sheaves, no transitivity and no sigma-compactness.

The source category is the existing `SectionActions.ActionSheaf G X`.
For each such sheaf `F`, `moduleObject hX F` is literally
`CompactSectionTestModule.compactSectionFunctor hX` on `underlying F`.
Its carrier is the original compact-support submodule of original global
sections, and its test action is the published locally constant scalar
action. The target `CompatibleTestAction` is the existing category of
nondegenerate modules over the pointwise test algebra, with their canonical
complex scalars and compatible representations.

## The covariance law

`global_germ_transport` specializes the existing labelled germ-transport
equation at the original global section arrow labelled by `g⁻¹`. The germ
at `x` of `g • s` is therefore the original stalk transport of the germ
of `s` at `g⁻¹ • x`. This equation has no fixed-point hypothesis.

`action_compatible` proves the exact law

```text
ρ(g)(f • s) = testRepresentation(g)(f) • ρ(g)(s).
```

It compares original germs using that transport equation, the published
formula `germ(f • s) = f(x) • germ(s)`, and complex linearity of the
original stalk transport. The translated test is exactly inverse pullback,
`testRepresentation g f x = f (g⁻¹ • x)`. Germ separation of the original
underlying sheaf proves equality of sections, and subtype extensionality
proves equality in the original compact-section space.

`canonicalScalar_eq` applies the published uniqueness result for the
complex scalars recovered from a nondegenerate test action. It identifies
that multiplication pointwise with the original complex multiplication on
compact sections. `canonicalAction` uses the original operators of
`SectionActions.compactRepresentation F`; the scalar equation proves their
linearity for the canonical complex structure. Their identity and product
laws are the existing representation laws. No new vector carrier or group
operator is introduced.

## Functors and smoothness

`compatibleObject` bundles these original data. `compatibleMap` uses the
published compact-section test-module map of the original underlying
sheaf morphism. The existing `CompactSections.map` intertwining equation
proves that this same map commutes with the group operators. `functor hX`
bundles these assignments; its identity and composition laws hold on the
original maps. `forgetIso` is the identity natural isomorphism with the
published ordinary compact-section functor after forgetting the actions.

`smoothProperty` imposes `Langlands.IsSmooth` on the whole original module
representation, and `SmoothCompatibleTestAction` is its full subcategory.
`smoothFunctor hX` lifts the same compact-section functor from the existing
`SmoothActionSheaf G X`. Its smoothness proof is exactly the source
object's smoothness of all compact sections, since the group operators are
unchanged. It does not replace the module by its smooth vectors.

These are constructions and their intrinsic laws for the forward direction
of III.3.1. The inverse equivariant sheaf construction, canonical comparison
maps, equivalence statement, induction sheaf and coinvariant sheaf remain
separate obligations.
