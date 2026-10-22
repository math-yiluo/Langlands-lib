# Compactly supported cohomology through the smooth Godement complex

Author: Worker 61. Built on Worker 61's smooth equivariant Godement complex
`Langlands.Sheaf.Equivariant.Godement.Smooth`, on Worker 13's smooth compact
sections `Langlands.Sheaf.Equivariant.SmoothSheafCompactSections` and invariant
compact sections `Langlands.Cohomology.SmoothSheafCohomology`, and on Worker
13's degree-zero result `EquivariantGodementCohomology.homologyZeroIso` in
`Langlands.Cohomology.EquivariantGodementCohomology`.

Let `R` be a commutative ring and `G` a topological group acting on a
topological space `X` by continuous translations, with `R`, `G` and `X` in one
universe `u`. Assume `HasStableNeighbourhoods G X`, as for the published
abelian category `SmoothTopologicalSheaf R G X` of smooth equivariant module
sheaves. For a smooth sheaf `F`, `Godement.smoothComplexFunctor R G X F` is
its smooth Godement complex: the iterated cokernel complex of the
degree-zero smooth Godement functor `T = Godement.smoothZeroFunctor R G X`
with its monic coaugmentation `F ⟶ T F`, computed in smooth sheaves.

## Smooth representations

`smoothGodementCompactComplex R G X` applies the smooth compact-section functor
`smoothSheafCompactSections R G X` termwise to the smooth Godement complex. That
functor sends a smooth sheaf to its compactly supported global sections, as a
smooth representation of `G`. The result is a cochain complex in
`SmoothRep R G`, functorial in `F`.
`smoothGodementCompactComplexToRepIso` identifies its underlying complex of
representations with the complex obtained by applying the compact-section
representation `CompactSections.functor R G X` to the terms of the smooth
Godement complex, viewed as equivariant sheaves through
`Langlands.Sheaf.Equivariant.smoothInclusion`. It is Mathlib's
`Functor.mapHomologicalComplexCompIso` applied to the published
`smoothSheafCompactSectionsToRepIso`.

`smoothGodementCompactCohomology R G X q` is degree-`q` homology of this
complex, computed in the abelian category `SmoothRep R G`.

## Invariant sections

`smoothGodementInvariantCompactComplex R G X` applies the published
`SmoothSheafCohomology.invariantCompactSections R G X` termwise instead. That
functor takes the compactly supported global sections fixed by every element
of `G`, as an `R`-module. The result is a cochain complex of `R`-modules.
`smoothGodementInvariantCompactCohomology R G X q` is its degree-`q` homology.

## Degree zero

`smoothGodementCompactCohomologyZeroIso` is a natural isomorphism between
degree-zero smooth Godement cohomology and `smoothSheafCompactSections R G X`.
`smoothGodementInvariantCompactCohomologyZeroIso` identifies the degree-zero
invariant cohomology with `SmoothSheafCohomology.invariantCompactSections
R G X`. Both are instances of `EquivariantGodementCohomology.homologyZeroIso`.
That result says the following. Let `T` be an endofunctor of an abelian
category and `η : 𝟭 ⟶ T` a coaugmentation with monic components. Let `Φ` be an
additive functor into an abelian category that preserves finite limits. Then
degree-zero homology of `Φ` applied termwise to the cokernel complex of
`(T, η)` is naturally isomorphic to `Φ`. Its three inputs are all published:
the smooth coaugmentation is monic (`Godement.mono_smoothCoaugmentation_app`),
and both section functors are additive and preserve finite limits. The
instances are `smoothSheafCompactSections_additive`,
`smoothSheafCompactSections_preservesFiniteLimits`,
`invariantCompactSections_additive` and
`invariantCompactSections_preservesFiniteLimits`.

## Provenance and scope

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished
1995–1996 manuscript), section 1.5, printed p.10, constructs the Godement
resolution `C^•(F)` from `C^0 = ν_* ν^*` and iterated cokernels. Printed p.11
defines `Γ_{c,X(G)}(F)`, the global sections over `X(G)` with compact support.
It defines `H^q_c(X(G), F)` as their derived functors. It also defines
`Γ_{c,X{G}}(F)`, the colimit of `Γ_{c,X(N)}(F)` over open subgroups `N`, with
derived functors `H^q_c(X{G}, F)`. Harris, *Galois properties of cohomological
automorphic forms on GL(n)*, J. Math. Kyoto Univ. 39-2 (1999), section 2,
printed p.304, uses Berkovich's smooth `G`-equivariant Godement construction
`T ↦ F(T)`. For an étale sheaf `T` of smooth modules, `F(T)` is a sheaf of the
same kind that is acyclic for compactly supported sections. Iterating it on
cokernels gives the resolutions of Lemma 2.2, which compute compactly
supported cohomology together with the smooth action of the stabilizer.
Worker 61 read these passages in the original.

This module is derived. It takes sections of the published smooth Godement
complex and then homology, in the ordinary-topological transport setting of
that complex. There, global sections of a sheaf on `X(G)` correspond to the
`G`-invariant global sections of the equivariant sheaf. So the invariant
variant corresponds to Berkovich's `Γ_{c,X(G)}`. The smooth variant
corresponds to `Γ_{c,X{G}}` with its `G`-action, since a compactly supported
section of a smooth sheaf is fixed by an open subgroup (the published
`CompactSections.isSmooth_representation_of_isSmoothSheaf`). These
correspondences explain the choice of section functors; the module does not
formalize `X(G)`, `X{G}` or the colimit over open subgroups.

The module proves only the constructions, the comparison of underlying
representation complexes and the degree-zero isomorphisms. It does not prove
exactness of the augmented complex beyond degree zero. It does not prove
flasqueness, softness or acyclicity of the smooth Godement terms (Berkovich
1.5 (i), Proposition 1.5.1; Harris p.304). It makes no comparison with the
derived functors `SmoothSheafCohomology.compactDerived` and
`SmoothSheafCohomology.invariantCompactDerived`. It makes no comparison with
the published `EquivariantGodementCohomology.smoothCompactComplex` and
`smoothCompactCohomology`. Those take the smooth part of compact sections of
the ordinary equivariant Godement complex of an arbitrary equivariant sheaf,
whereas this module uses the smooth Godement complex of a smooth sheaf. The
setting is not Berkovich's analytic étale site, and geometric points are
replaced by ordinary points of the topological space.

Source registrations:
Berkovich,
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
member SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
Harris 1999, `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`,
SHA-256 `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
