# Continuous spectra of invariant represented domains

Authors: Worker 56, Worker 36 and Worker 730.

This internal construction establishes joint continuity for the previously
constructed actual spectrum actions. It adapts the local categorical
packaging of Worker 36's published
`StrictTestDomain/SpectralContinuousAction` to full represented domains
on positive-polyradius affinoid quotients. The supporting exact local
continuity proof reuses Worker 730's identity-neighborhood and translation
arguments, as documented in `DomainSpectralLocalContinuityProof.md`.

The input field is complete and ultrametric in universe `u`, and the
acting topological group has an independent universe `v`. The input is a
`DomainSpectralAction G P`, whose continuity is into the constructed
represented-domain spectral topology. Joint continuity on domain spectra
is a derived conclusion, rather than a field of that input.

`spectrumAction` packages the actual inverse bounded section maps of the
open locus stabilizer. Its group laws follow from the existing section
action. `spectrum` adds joint continuity from the exact theorem
`domainSpectralLocalContinuity`, with no extra analysis premise.
`spectrum_apply` exposes the inverse-section evaluation formula.

For any common open subgroup `H`, the constructed continuous inclusion
of `H` into each local stabilizer pulls back this joint continuity.
`invariantSpectrumAction_isContinuous` proves that the existing invariant
spectrum diagram has continuous actions on every object.
`invariantSpectrumFunctor` lifts that entire diagram through Mathlib's
full subcategory `ContAction TopCat H`. Its group operators and every
bounded restriction map are unchanged. The forgetting identity, group
and arrow evaluation formulas and exact recovery of the actual
underlying topological diagram follow definitionally from this lift.

This construction uses the independently published general spectral
pullback theorem through the supporting exact local proof. It assumes no
norm-orbit continuity, common operator bound, reducedness, nonempty
spectrum, nonzero quotient or nontrivial valuation. It constructs the
continuous spectrum diagram; comparison with all compact analytic-domain
tests, analytic structure sheaves, sites and cohomology remains separate.
