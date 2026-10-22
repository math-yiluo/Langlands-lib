# Derived compact section complexes of smooth equivariant sheaves

Author: Worker 13. Specializes Worker 13's `Langlands.Cohomology.DerivedPlus`
to the compact section functors of Worker 13's
`Langlands.Cohomology.SmoothSheafCohomology` and
`Langlands.Sheaf.Equivariant.SmoothSheafCompactSections`.

Let `R` be a commutative ring and `G` a topological group acting on a
topological space `X` by continuous translations, with
`HasStableNeighbourhoods G X`, all in one universe `u`. Smooth equivariant
module sheaves form the abelian category `SmoothTopologicalSheaf R G X` with
enough injectives. Derived categories are chosen by instances
`HasDerivedCategory.{w}` on that category, `HasDerivedCategory.{w'}` on
`Langlands.SmoothRep R G` and `HasDerivedCategory.{w''}` on `ModuleCat R`,
with independent universes. Each can be supplied by Mathlib's
`HasDerivedCategory.standard`.

## Definitions and results

- `compactComplex R G X` is the derived complex
  (`DerivedPlus.derivedComplex`) of `smoothSheafCompactSections R G X`, with
  values in `DerivedCategory.Plus (SmoothRep R G)`.
- `compactComplexHomologyIso F q` identifies its degree `q` cohomology, for
  `q : ℕ`, with `(SmoothSheafCohomology.compactDerived R G X q).obj F`. This
  is `DerivedPlus.homologyIso` for Mathlib's chosen injective resolution of
  `F` in the smooth category.
- `isZero_compactComplex_homology` proves vanishing in negative degrees.
- `invariantCompactComplex R G X` is the derived complex of
  `SmoothSheafCohomology.invariantCompactSections R G X`, with values in
  `DerivedCategory.Plus (ModuleCat R)`.
  `invariantCompactComplexHomologyIso` and
  `isZero_invariantCompactComplex_homology` are the corresponding results.

## Provenance and scope

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished
1995–1996 manuscript), section 1.5, printed p.11, defines `H^q_c(X{G}, F)` and
`H^q_c(X(G), F)` as derived functors of compactly supported sections.
`SmoothSheafCohomology` explains in which sense its derived functors have
these shapes. Harris, *Galois properties of cohomological automorphic forms on
GL(n)* (1999), Proposition 4.4, printed p.309, takes `Ext` in the category of
smooth representations against compactly supported cohomology. Worker 13 read
these passages in the original. `compactComplex` packages the derived compact
sections as one object of the bounded below derived category of smooth
representations. After the inclusion `DerivedCategory.Plus.ι`, that object is
the form of input used by Worker 3's published
`Langlands.Cohomology.HyperextDegenerationStatement`.

Not treated: boundedness above, the hyperext spectral sequence, comparison
with the Godement route or with Harris's projective complexes, naturality of
the cohomology isomorphisms in `F`, and the analytic étale site.

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

All imported modules are present in Library commit
`e3c2fa98be720f63c6981efbbdf15cd223329e76`.
