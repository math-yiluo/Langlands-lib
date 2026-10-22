# Derived sections and compact support

Author: Worker 13.

This module constructs right-derived compact sections and ordinary sections
on actual module sheaves over a topological space. Both the space and the
coefficient ring use universe `u`, and the sheaf values are `ModuleCat.{u} R`.
Mathlib proves this sheaf category is Grothendieck abelian and supplies enough
injectives and injective resolutions. No injective resolution, desired
cohomology module or comparison theorem is postulated as a project field.

`compactComplex F` applies the compact-section functor from the accompanying
file to Mathlib's chosen injective resolution. `compactHomotopyFunctor`
packages the result functorially in the homotopy category.
`compactCohomology n` then takes its homology. The representative and homology
isomorphisms are obtained from Mathlib's proved injective-resolution
construction. Choice of resolutions is not claimed to give a strictly
functorial complex before passing to homotopy.

The natural inclusion of compact sections into ordinary sections yields
`forgetSupportHomotopy` and `forgetSupport n`. Both section functors preserve
finite limits: ordinary sections are evaluation after the sheaf inclusion,
and the compact-section kernel argument is proved in the accompanying file.
The module supplies the resulting natural degree-zero isomorphisms
`compactCohomologyZeroIso` and `ordinaryCohomologyZeroIso`.

Functoriality transports algebraic actions by fixed-space sheaf automorphisms
to cohomology. It also constructs diagrams of cohomology modules from actual
coefficient diagrams, compatibly with forgetting support. This neither proves
commutation of cohomology with inverse limits nor constructs an action moving
the base space. No smoothness or Galois-continuity assertion is implicit.

The source is Berkovich, *Etale equivariant sheaves on p-adic analytic spaces*,
unfinished 1995-1996 manuscript, section 1.5, pp.11-12: compact-support
cohomology is defined through the higher derived section functors. This file
implements the ordinary-topological construction in Mathlib's existing
homological algebra. The analytic-etale, equivariant and Harris Shimura
specializations, the Godement acyclicity comparison, and the spectral sequence
are separate obligations, not conclusions of this construction.

Registered source folder
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
SHA-256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
Worker 13 read the cited original pages.

Formal dependencies: accompanying `Langlands.Sheaf.CompactSupport`,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435` with Lean 4.34.0,
especially Grothendieck sheaf categories, enough injectives, right-derived
functors and action categories.

The companion pair `Langlands/Geometry/EtaleDerivedSections` independently
instantiates ordinary derived sections on the genuine small-etale site of
a scheme. It supplies the general cohomology operation used in the target
of Harris 1999 Proposition 4.4, p.309, equation (4.4.1), while retaining the
Shimura and uniformization specializations as obligations. That pair cites
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, PDF SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
Neither module asserts a comparison between the topological and scheme
etale constructions.
