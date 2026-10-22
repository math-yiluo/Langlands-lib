# Compactly supported sections of smooth equivariant sheaves

Author: Worker 13. Built on Worker 13's published
`Langlands.Sheaf.Equivariant.CompactSupport` (the compact-section
representation `CompactSections.representation` and functor
`CompactSections.functor`), `Langlands.Cohomology.EquivariantDerivedSections`
(left exactness of that functor) and `Langlands.Representation.Category.Abelian`
(the abelian category `Langlands.SmoothRep R G`), and on `SmoothAbelian` (this
submission).

Let `R` be a commutative ring and `G` a group with a topology acting on a
topological space `X` by continuous translations (`ContinuousConstSMul`). The
space, ring and module carriers lie in a universe `u`. In the first two
sections below `G` lies in a universe `uG`.

## Compact sections of smooth sheaves are smooth

`CompactSections.restrict_sectionAction_eq`: let `H` be a subgroup and `V` an
`H`-stable open on which `H` fixes the restriction of a global section `s`.
Then for `h ∈ H` the translate `h • s` and `s` have the same restriction to
`V`. Composing the subgroup arrow of `h` with the inclusion of `V` equals
composing the inclusion with the global transport arrow of `h`.

`CompactSections.isSmooth_representation_of_isSmoothSheaf`: if `F` is a smooth
equivariant module sheaf, then the compact-section representation of `F` is
smooth in the published sense `Langlands.IsSmooth`. Every compactly supported
global section is thus fixed by an open subgroup. No Hausdorff or local
compactness hypothesis on `X` is used. The proof applies Mathlib's induction
principle for compact sets (`IsCompact.induction_on`) to the support of `s`.
The property is: some open subgroup `H` and some `H`-stable set `W` containing
the subset satisfy that the germs of `h • s` and `s` agree at every point of
`W` for `h ∈ H`.

- The empty set takes `H = G` and `W = ∅`. The property passes to subsets.
- For a union of two sets, intersect the subgroups and unite the sets.
- Near a point of the support, smoothness of `F` gives an open neighbourhood
  stable under and fixing `s` for some open subgroup. The germs agree there by
  `restrict_sectionAction_eq`.

For the resulting `H` and `W`, two sections of the underlying ordinary sheaf
with the same germs everywhere are equal (Mathlib's `section_ext`). On `W` the
germs agree. Outside `W` the germ of `s` vanishes because the support lies in
`W`. The germ of `h • s` vanishes too: the published `support_action_subset`
puts its support inside `h` times the support of `s`, and `W` is `H`-stable.

## The functor to smooth representations

`smoothSheafCompactSections R G X` is the functor from
`SmoothTopologicalSheaf R G X` to `Langlands.SmoothRep R G` lifting
`smoothInclusion R G X ⋙ CompactSections.functor R G X` through the published
smooth subcategory. `smoothSheafCompactSectionsToRepIso` identifies its
composite with `Langlands.SmoothRep.toRep` with that composite (Mathlib's
`ObjectProperty.liftCompιIso`). Carriers, actions and intertwiners are those
of the compact-section representations.

## Left exactness

Now `G` is a topological group in the universe `u`, with
`HasStableNeighbourhoods G X`.

- `smoothInclusion_preservesFiniteLimits`: the inclusion of smooth sheaves
  preserves kernels, as the smooth subcategory is closed under kernels, hence
  preserves finite limits. `smoothInclusion_additive` follows.
- `smoothSheafCompactSections_preservesFiniteLimits`: the composite of the
  inclusion with the published left exact `CompactSections.functor` preserves
  finite limits. So does `smoothSheafCompactSections` followed by `toRep`,
  through the isomorphism above, and `toRep` is fully faithful.
  `smoothSheafCompactSections_additive` follows.

## Provenance and scope

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished
1995–1996 manuscript), section 1.5, printed p.11, defines the support of a
section by its nonzero germs and
`Γ_{c,X{G}}(F) = lim_N Γ_{c,X(N)}(F)`, the colimit over open subgroups `N` of
compactly supported `N`-invariant sections. Worker 13 read this passage in the
original. For a smooth sheaf this colimit is the union, over open subgroups,
of the compactly supported sections they fix. By
`isSmooth_representation_of_isSmoothSheaf` that union is all compactly
supported sections. So on smooth sheaves `smoothSheafCompactSections` has the
shape of Berkovich's `Γ_{c,X{G}}` with its `G`-action, on the published
ordinary-topological transport site. The module does not construct the
colimit or prove such an identification as a declaration. It does not treat
the analytic étale site.

Source registration:
Berkovich,
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
member SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

All imported modules other than `SmoothAbelian` and `SmoothPart` are present
in Library commit `9a0767626050f3346ad5f25e37cef39f38a5c0dc`.
