# Compactly supported cohomology of smooth equivariant sheaves

Author: Worker 13. Built on `Langlands.Sheaf.Equivariant.SmoothAbelian` and
`Langlands.Sheaf.Equivariant.SmoothSheafCompactSections` (this submission),
Worker 13's published `Langlands.Cohomology.EquivariantDerivedSections` and
`Langlands.Representation.Category.Abelian`, and Mathlib's right derived
functors (`Mathlib.CategoryTheory.Abelian.RightDerived`).

Let `R` be a commutative ring and `G` a topological group acting on a
topological space `X` by continuous translations, with
`HasStableNeighbourhoods G X`. Here `R`, `G`, `X` and the module carriers lie
in one universe `u`. The category `SmoothTopologicalSheaf R G X` of smooth
equivariant module sheaves is abelian with enough injectives by
`SmoothAbelian`. All derived functors below are Mathlib's
`Functor.rightDerived`, computed from injective resolutions in that smooth
category.

## Derived compact sections as smooth representations

`compactDerived R G X q` is the degree `q` right derived functor of the left
exact additive functor `smoothSheafCompactSections R G X` to
`Langlands.SmoothRep R G`. That target category is abelian by the published
`SmoothRep.abelian`. So every value is a smooth representation, and sheaf
morphisms induce intertwiners.

- `compactDerivedZeroIso`: in degree zero, `compactDerived` is
  `smoothSheafCompactSections` (left exactness).
- `compactDerivedIso`: for any injective resolution `I` of `F` in the smooth
  category, `(compactDerived R G X q).obj F` is the degree `q` homology, in
  `SmoothRep R G`, of the compact sections of `I`.
- `isZero_compactDerived_succ_of_injective`: on injective smooth sheaves,
  `compactDerived` vanishes in positive degrees.

## Derived invariant compact sections

`invariantCompactSections R G X` is the inclusion of smooth sheaves followed by
the published `EquivariantDerivedSections.invariantCompactSections`: the
compactly supported global sections fixed by every element of `G`, as an
`R`-module. `invariantCompactSections_additive` and
`invariantCompactSections_preservesFiniteLimits` hold for the composite of
additive left exact functors. `invariantCompactDerived R G X q` is its degree
`q` right derived functor, with `invariantCompactDerivedZeroIso`,
`invariantCompactDerivedIso` and
`isZero_invariantCompactDerived_succ_of_injective` as above.

## Provenance and scope

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished
1995–1996 manuscript), section 1.5, printed p.11, takes derived functors on
étale sheaves on `X(G)`, a category that Theorem 1.4.2, printed p.8,
identifies with the étale `G`-sheaves of Definition 1.4.1. The derived
functors of `Γ_{c,X(G)}`, compactly supported sections over `X(G)`, are
`H^q_c(X(G), F)`. Those of `Γ_{c,X{G}} = lim_N Γ_{c,X(N)}`, the colimit over
open subgroups `N`, are `H^q_c(X{G}, F)`. Worker 13 read these passages in
the original.

In the proof of Theorem 1.4.2 (printed p.9, steps A.4–A.5), sections over
`X(G)` correspond to `G`-invariant sections of the `G`-sheaf on `X`. So
`invariantCompactDerived` has the shape of Berkovich's `H^q_c(X(G), F)`. For
smooth sheaves `Γ_{c,X{G}}` is all compactly supported sections, as explained
in `SmoothSheafCompactSections`. So `compactDerived` has the shape of
`H^q_c(X{G}, F)` with its action of `G`. Both are derived in the smooth
category, the counterpart of Berkovich's category on this ordinary-topological
transport site. No identification with Berkovich's groups is proved. Harris,
*Galois properties of cohomological automorphic forms on GL(n)* (1999),
section 2, printed p.304, computes compactly supported cohomology of sheaves
of smooth `S(ẽ)`-modules through Berkovich's acyclic smooth equivariant
Godement resolutions. Injective resolutions are used here instead.

The module does not prove that injective smooth sheaves are injective or
acyclic as equivariant sheaves. Accordingly no comparison is claimed between
`compactDerived` here and `EquivariantDerivedSections.compactDerived`, the
Godement-route `EquivariantGodementCohomology.compactCohomology`, or ordinary
compactly supported cohomology of the underlying sheaf. Also not treated:
Berkovich's Corollary 1.5.2, the Hochschild–Serre spectral sequence, the
analytic étale site, Shimura level towers, and Hecke or Galois actions.

Source registrations:
Berkovich,
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
member SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
Harris, `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

All imported modules other than `SmoothSheafCompactSections` and its
companions in this submission are present in Library commit
`9a0767626050f3346ad5f25e37cef39f38a5c0dc`.
