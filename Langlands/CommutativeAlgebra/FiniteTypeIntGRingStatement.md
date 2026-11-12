# Finite-type integer algebras are G-rings: statement

Module: `Langlands.CommutativeAlgebra.FiniteTypeIntGRingStatement`.

Author: Worker 116. This prerequisite is part of the agreed arithmetic
completion branch of Task 5157.

`FiniteTypeIntGRingStatement.{u}` asserts that every commutative ring
`S : Type u` which is a finite-type algebra over the integers satisfies the
imported predicate `IsGRing S`. The integer algebra structure is the
canonical one. No domain, reducedness, locality, characteristic, smoothness
or regularity hypothesis is added to `S`. The universe `u` is arbitrary.

By the imported definition of `IsGRing`, the conclusion includes
Noetherianity of `S` and, for every prime ideal `p` of `S`, regularity of the
canonical algebra map from `P = Localization.AtPrime p` to
`AdicCompletion (IsLocalRing.maximalIdeal P) P`. This includes all the
maximal ideals required by finite-type integer etale approximation and
also includes nonmaximal primes. `RegularAlgebra` means flatness with
Noetherian geometrically regular actual tensor-product fibres.

## Original source

The source is Stacks Project, More on Algebra, Section 15.51 (Tag 07GG),
Proposition 15.51.12, parts (3) and (5). Part (3) states that the integers
are a G-ring, and part (5) gives the finite-type extensions of the listed
rings. Its proof refers to Proposition 15.51.10 for ascent along
essentially finite-type maps.

The retained original page is `07GG.html` in the registered source
`stacks-regular-maps-g-rings-2026-11-11`, folder-content SHA-256
`b646b6100f8f6ecd5e6a8a07f74031a8350d9bf77c1c9538fc113a7cc250fdcc`.
The page was retrieved on 11 November 2026 from
<https://stacks.math.columbia.edu/tag/07GG>. In this retained page, ascent
is Proposition **15.51.10**; 15.51.11 is a remark about completion not
preserving the G-ring property. This corrects the descriptive locator in
the source bundle's README without modifying the original source.

## Proof and consumer obligations

This file introduces a proposition-valued definition and no proof of it.
A separate proof must establish the integer G-ring input and finite-type
ascent, or another complete argument, using proved inputs.

Once the proposition is proved, `IsGRing.regularAlgebra_completion` can
specialize its conclusion to any maximal ideal. Neither Popescu
factorization, Noetherianity of the completion itself, finite-order
smooth-to-etale comparison nor the final
`FiniteTypeIntEtaleCompletionApproximationStatement` is proved here.
Those remain independent obligations; this proposition is not an extra
premise of the unchanged final target.
