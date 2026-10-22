# Derived equivariant sections

Author: Worker 13.

This module constructs right derived functors of the section functors on the
published category `TopologicalSheaf G X (ModuleCat R)` of equivariant module
sheaves on a moving-space action. Here `R`, the group `G` and the space `X`
lie in one universe `u`, `G` is an abstract group acting on `X`, and every
translation is continuous (`ContinuousConstSMul`). The companion module
`Langlands.Sheaf.Equivariant.Abelian` proves that this sheaf category is
abelian with enough injectives. Mathlib's `Functor.rightDerived` therefore
computes each derived functor below from a chosen injective resolution in that
category.

## Left exactness

`sectionRepresentationForgetIso` identifies the module underlying the global
section representation with evaluation on the whole space. Similarly,
`compactSectionsForgetIso` identifies the module underlying the compact
section representation with the published ordinary compact-section functor
`Langlands.Sheaf.CompactSupport.functor`, applied to the underlying ordinary
sheaf. Both isomorphisms have identity components. The forgetful functor from
`Rep R G` to `ModuleCat R` reflects limits. Evaluation preserves finite limits
by `Langlands.Sheaf.Equivariant.Limits`, and the underlying sheaf functor
preserves finite limits by the same module. The ordinary compact-section
functor preserves finite limits by `Langlands.Sheaf.CompactSupport`. Hence
`sectionRepresentation_preservesFiniteLimits` and
`compactSections_preservesFiniteLimits` prove that both representation-valued
functors are left exact.

## Derived representations

`globalDerived R G X q` and `compactDerived R G X q` are the degree `q` right
derived functors of global and compact sections. They are functors from
equivariant module sheaves to `Rep R G`, so every value carries a group action
together with intertwining maps for sheaf morphisms. `forgetSupport` derives
the inclusion of compact sections into global sections.

Left exactness gives the degree-zero isomorphisms `globalDerivedZeroIso` and
`compactDerivedZeroIso` with the section functors themselves.
`globalDerivedIso` and `compactDerivedIso` identify the derived values at `F`
with the homology representations, from the published
`Langlands.Cohomology.EquivariantSections`, of the section complexes of any
injective resolution of `F`. The theorems
`isZero_globalDerived_succ_of_injective` and
`isZero_compactDerived_succ_of_injective` prove vanishing in positive degrees
on injective equivariant sheaves. `compactDerivedDiagram` applies
`compactDerived R G X q` to a diagram of equivariant sheaves, for example an
inverse system of coefficient sheaves. It keeps every transition map and takes
no limit.

## Invariant sections

`invariantGlobalSections` and `invariantCompactSections` compose the section
representations with Mathlib's invariants functor `Rep.invariantsFunctor`.
This functor is a right adjoint of the trivial-representation functor, hence
left exact, so both composites are left exact. `invariantGlobalDerived` and
`invariantCompactDerived` are their module-valued right derived functors.
The module also gives degree-zero isomorphisms and, for invariant compact
sections, the injective-resolution formula.

## Provenance and scope

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces*, unfinished
1995–1996 manuscript, section 1.5, printed p.11, defines the support of a
section by its nonzero germs. It defines `H^q_c(X(G), F)` as the values of the
higher derived functors of `F ↦ Γ_{c,X(G)}(F)`, the sections of `F` over `X(G)`
with compact support. Corollary 1.5.2, printed pp.11–12, concerns the action
of `G` on `H^q_c(X, b^* F)`. Harris, *Galois properties of cohomological
automorphic forms on GL(n)*, J. Math. Kyoto Univ. 39-2 (1999), section 2,
printed pp.303–306, studies compactly supported cohomology of the open subsets
`U(ẽ)` of Drinfeld's coverings with the smooth action of the compact open
stabilizer `S(ẽ)`. On printed p.304 it computes this cohomology with
Berkovich's smooth equivariant Godement-type resolutions, which are acyclic for
compactly supported sections. Worker 13 read these passages in the original.
The present module uses injective resolutions instead and makes no comparison
with that route.

These constructions are internal derived infrastructure on ordinary
topological spaces. They are not the analytic etale construction. The group
carries no topology, so the equivariant category corresponds to Berkovich's
setting only for a discrete group. `invariantCompactDerived` follows the shape
of Berkovich's definition of `H^q_c(X(G), F)` in this ordinary-topological,
discrete-group setting. `compactDerived` keeps the whole representation
instead of its invariants.

The module does not prove that the module underlying `compactDerived` or
`globalDerived` agrees with ordinary compactly supported or global sheaf
cohomology of the underlying sheaf. Such a comparison needs injective, or
suitably acyclic, underlying sheaves of equivariant injectives. Nor does it
assert smoothness or discreteness of the action on derived values, a spectral
sequence from group cohomology, comparison with the Godement resolution,
analytic etale sites, Shimura level towers, Hecke or Galois actions, or
Harris's Ext spectral sequence. These remain separate obligations.

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

The imported equivariant sheaf category, its abelian structure and limits, the
section representations and complexes, and the ordinary compact-section
functor are present in Library commit
`481ac9c36dcbe49e0ff1a50bb1855dc75a101e88`.
