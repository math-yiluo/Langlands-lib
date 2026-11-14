# Composite comparison for injective-preserving smooth section functors

Author: Worker 280.

This internal generalization of the published
`Langlands.Cohomology.EquivariantComposite.GlobalProof` replaces its specific
section-representation functor by any additive functor
`S : C ⥤ SmoothRep R G` preserving injective objects. The coefficient and group
universes are independent. The source `C` is abelian with enough injectives
and a model of its derived category. The derived-category model of smooth
representations is an independent instance. The group has a topology. No compatibility between multiplication and
that topology or compactness assumption is needed for this algebraic step.

Let `I` be an injective resolution of `F`. The integer extension of `I` is
bounded below with injective terms. Since `S` preserves injectives, the
termwise image `K = S(I)` has injective terms and is K-injective by Mathlib's
`CochainComplex.isKInjective_of_injective`. This proves the instance
`smoothSectionResolution_isKInjective`.

`smoothGlobalComparisonOfResolution` composes four additive equivalences:

1. The inverse of the published `resolutionRightDerivedIso` identifies
   `R^n(S ⋙ invariants)(F)` with the homology of the integer-indexed invariant
   resolution, with scalar multiplication forgotten.
2. This module's imported `invariantsHomologyIso` identifies that group with
   the homology of the termwise Hom complex from `trivialSmoothRep R G` to `K`.
3. The published `homologyDerivedAddEquiv` identifies that homology with
   morphisms from the trivial representation in degree zero to `K[n]` in
   the derived category. It applies because `K` is K-injective.
4. The inverse of the published `AcyclicResolution.derivedResolutionIso`,
   shifted by `n`, transports the target to the existing
   `DerivedPlus.derivedComplex S` evaluated at `F`.

`smoothGlobalComparisonOfResolution_naturality` proves naturality for a map
of injective resolutions. Its three squares are the published naturality of
`resolutionRightDerivedIso`, naturality of `invariantsHomologyIso`, and the
published `homologyDerivedAddEquiv_naturality`, followed by the inverse
naturality square of `derivedResolutionIso`. The proof evaluates the first
two squares on an element and combines the remaining compositions by
functoriality of shift.

`smoothGlobalComposite` chooses Mathlib's injective resolutions, applies the
comparison above, and uses `DerivedPlus.descHom` to lift every coefficient
morphism. Its conclusion includes the complete naturality equation; no
comparison is assumed as input. This generic result is the common algebraic
step for the étale and quasi-étale specializations of Berkovich's composite
identification. Its provenance is the indicated Library proofs rather than
an independent claim that Berkovich states this abstract formulation.
