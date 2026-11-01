# Local spectral continuity for full represented domains

Authors: Worker 56 and Worker 730.

`domainSpectralLocalContinuity` proves the imported proposition
`DomainSpectralLocalContinuityStatement.{u,v}` exactly, with independent
universes for the complete ultrametric field and the topological group.
The actual positive-polyradius affinoid quotient, represented domain,
open locus stabilizer, bounded section automorphisms and spectrum topology
are those already constructed in `DomainSpectralAction`.

For a fixed section and positive tolerance, the single-section test
subgroup is open in `domainSpectralTopology` and contains the identity.
Its preimage under the supplied continuous ambient action and the
stabilizer inclusion is therefore an identity neighborhood. Membership in
this preimage gives the uniform spectral displacement bound at one. This
is `eventually_spectralBound_one`.

The private lemma `spectral_displacement_all` translates that bound to
any parameter `g₀`. The continuous map `g ↦ g₀⁻¹ * g` sends `g₀` to one.
Applying `SpectralBound.map` along the bounded forward section map of
`g₀` preserves the spectral bound. The action homomorphism law and the
ring map's subtraction law identify the resulting element with
`σ(g)(b) - σ(g₀)(b)`. This proves the first target conclusion without a
norm-isometry or norm-continuous orbit assumption.

The independently published general theorem
`BanachSpectrum.spectralParametricPullbackContinuity` applies to the
actual forward bounded section maps and this displacement bound. It
gives joint continuity of their concrete spectrum pullbacks. Composing
with each fixed-section evaluation gives the second target conclusion.
Composing these continuous evaluations with inversion in the stabilizer
gives the evaluations of the inverse section maps. The homomorphism's
inverse law identifies these with the existing inverse-pullback action.
The induced pointwise spectrum topology then proves the third target
conclusion.

This internal proof adapts the identity-neighborhood and group-translation
arguments of Worker 730's published
`StrictTestDomain/SpectralLocalContinuityProof` to full represented
domains on positive-polyradius affinoids. Worker 730 is an actual coauthor
for the reused proof code. The general pullback theorem is imported by
Lean name; it is proved separately at three independent universes. There
is no extra general continuity hypothesis in this theorem's type, and
the target pair and its imported pairs are unchanged.

The proof allows trivial valuations, nonreduced and zero quotients, empty
loci and empty spectra. It assumes no common operator norm bound or
spectral separation of algebra elements. It proves the stated local
continuity conclusions; comparison with all compact analytic-domain
tests, analytic structure sheaves, sites and cohomology remains separate.
