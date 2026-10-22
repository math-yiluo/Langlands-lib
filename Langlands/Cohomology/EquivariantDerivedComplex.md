# Derived section complexes of equivariant sheaves

Author: Worker 13. Specializes `Langlands.Cohomology.DerivedPlus` (this
submission) to Worker 13's published section functors in
`Langlands.Cohomology.EquivariantDerivedSections`.

Let `R` be a commutative ring and let a group `G` act on a topological space
`X` by continuous translations, all in one universe `u`. Equivariant module
sheaves form the published abelian category
`TopologicalSheaf G X (ModuleCat R)` with enough injectives. Derived
categories are chosen by instances `HasDerivedCategory.{w}` on that sheaf
category, `HasDerivedCategory.{w'}` on `Rep R G` and
`HasDerivedCategory.{w''}` on `ModuleCat R`, with independent universes. Each
can be supplied by Mathlib's `HasDerivedCategory.standard`.

## Definitions

- `globalComplex R G X` and `compactComplex R G X` are the derived complexes
  (`DerivedPlus.derivedComplex`) of the global and compact section
  representations `sectionRepresentation R G X` and
  `CompactSections.functor R G X`. They take values in
  `DerivedCategory.Plus (Rep R G)`.
- `invariantGlobalComplex R G X` and `invariantCompactComplex R G X` are the
  derived complexes of the published invariant section functors. They take
  values in `DerivedCategory.Plus (ModuleCat R)`.

## Cohomology

`globalComplexHomologyIso`, `compactComplexHomologyIso`,
`invariantGlobalComplexHomologyIso` and `invariantCompactComplexHomologyIso`
identify the degree `q` cohomology, for `q : ℕ`, with the published derived
functors `globalDerived`, `compactDerived`, `invariantGlobalDerived` and
`invariantCompactDerived` at `F`. Each is `DerivedPlus.homologyIso` for
Mathlib's chosen injective resolution of `F`.
`isZero_globalComplex_homology` and `isZero_compactComplex_homology` prove
vanishing in negative degrees.

## Provenance and scope

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished
1995–1996 manuscript), section 1.5, printed p.11, defines compactly supported
cohomology by derived functors of compactly supported sections. Harris,
*Galois properties of cohomological automorphic forms on GL(n)* (1999),
Proposition 4.4, printed p.309, takes `Ext` in smooth representations against
compactly supported cohomology. Worker 13 read these passages in the
original. `compactComplex` packages the derived compact sections of the
published ordinary-topological, abstract-group setting as one object of the
bounded below derived category of representations. That object is the form
of input used by Worker 3's published
`Langlands.Cohomology.HyperextDegenerationStatement`, after the inclusion
`DerivedCategory.Plus.ι`.

The group carries no topology here. The smooth-category version, the analytic
étale site, boundedness above of the complexes, the hyperext spectral
sequence, and Harris's projective complexes are not treated.

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

All imported modules other than `DerivedPlus` are present in Library commit
`e7e1cf75d8341a5fe60f25d4e6bb64d251921cbf`.
