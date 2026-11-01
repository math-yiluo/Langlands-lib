# Actual spectra of represented-domain spectral spaces

Authors: Worker 56, Worker 36 and Worker 730.

This internal construction adapts the spectrum part of the published
`GeneralizedAffinoid/NormContinuousAction` to the full category
`DomainSpectralActionCategory`. Its continuity property tests actual
sections on full represented domains of positive-polyradius affinoids.
The input field is complete and ultrametric, and the topological group's
universe is independent. The supporting local continuity proof reuses
Worker 730's code, as explained in `DomainSpectralLocalContinuityProof.md`.

`spectrumMap_equivariant` proves that pullback along every equivariant
bounded algebra map intertwines the inverse-pullback spectrum actions.
For each algebra element it applies the arrow's forward equivariance
equation at the inverse group element, then evaluates that equality with
the actual target seminorm. No faithfulness of spectrum evaluation is
used. This lemma itself needs no topological-group instance.

`spectrumFunctor` maps the opposite category `DomainSpectralSpace K G`
to `ContAction TopCat G`. Each object uses the derived global joint
continuity construction. Every arrow is pullback along its original
bounded algebra map; there are no further restrictions on arrows.
Identity and composition follow by extensionality and evaluation of
these actual bounded pullbacks.

The object and arrow evaluation formulas expose the inverse group
operators and bounded-map pullbacks. `spectrumFunctor_forget` identifies
the underlying topological-space diagram with the existing affinoid
spectrum functor after forgetting the action.

There is no extra analysis premise: the exact local continuity theorem
and its published general spectral proof supply the joint continuity.
The construction asserts no comparison between norm and represented-domain
spectral topologies, full analytic automorphism topology, general
analytic spaces, sites or cohomology. Empty spectra, zero and nonreduced
quotients, and trivial scalar valuations remain allowed.
