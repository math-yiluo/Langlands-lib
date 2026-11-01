# Local spectral continuity for represented affinoid domains

Authors: Worker 56 and Worker 36.

`DomainSpectralLocalContinuityStatement.{u,v}` is a proposition definition.
It states three conclusions about the already constructed local section
action. This pair supplies no proof.

Let `K : Type u` be a complete ultrametric normed field, let
`P : PresentedAffinoidAlgebra K` be an actual positive-polyradius affinoid
quotient, and let `G : Type v` be a topological group. The two universes are
independent. Fix `ρ : DomainSpectralAction G P`, whose actual bounded
automorphism homomorphism is continuous into the explicitly constructed
`domainSpectralTopology P`.

Fix any `d : Domain K P`. This is a full represented affinoid domain, with
its actual section algebra `d.algebra`, structural bounded map, spectrum
image and unique bounded factorization property against all presented
positive-polyradius affinoid test algebras. The statement does not restrict
`d` to a unit-radius rational presentation.

Write `H = ρ.locusOpenSubgroup d` and `σ = ρ.sectionAction d`. The subgroup
`H` has the inherited subspace topology from `G`. It is the constructed
open subgroup preserving `d.locus` setwise under the inverse-pullback
spectrum action. The homomorphism `σ : H →* Aut d.algebra` consists of
actual bounded section automorphisms constructed by the full domain
factorization property. No new section maps or group laws are assumed.

The first conclusion says that for each fixed section `b : d.algebra`,
each `g₀ : H` and each real `ε > 0`, eventually as `g` approaches `g₀` in
`H`,

`SpectralBound (σ(g)(b) - σ(g₀)(b)) ε`.

The imported predicate means that every `x : BanachSpectrum d.algebra`
satisfies `x(σ(g)(b) - σ(g₀)(b)) ≤ ε`. A single neighborhood controls all
spectrum points for the fixed `b`, `g₀` and `ε`; it may depend on these
three inputs. The tolerance is positive, and the bound is non-strict.

The second conclusion is joint continuity of the real-valued map

`H × BanachSpectrum d.algebra → ℝ, (g,x) ↦ x(σ(g)(b))`

for each fixed section `b`. The spectrum has the existing topology of
pointwise convergence of bounded multiplicative seminorms, and the domain
has the product topology.

The third conclusion is joint continuity of the actual spectrum action

`H × BanachSpectrum d.algebra → BanachSpectrum d.algebra, (g,x) ↦ σ(g) • x`.

The existing action uses inverse pullback:
`(σ(g) • x)(b) = x(σ(g).inv(b))`. Thus the second conclusion concerns
forward section evaluation, while the third uses the inverse bounded
section operator.

This is an internal consequence target for the constructed represented
domain topology. It adapts Worker 36's published
`StrictTestDomain/SpectralLocalContinuityStatement` to arbitrary full
represented domains on positive-polyradius affinoids. The existing
`DomainAutomorphism`, `DomainSpectralTests`, `DomainSpectralTopology` and
`DomainSpectralAction` constructions supply its concrete inputs.

The intended derivation first pulls back an open positive single-section
test to obtain uniform displacement control at the identity. Translation
in `H` and pullback along a bounded section operator give the first
conclusion at every parameter. The seminorm difference inequality
`|x(a) - x(c)| ≤ x(a-c)` and continuity of fixed-section evaluation then
give the second conclusion. The spectrum's pointwise topology and
continuous inversion in `H` give the third conclusion. These steps are
proof obligations, not additional hypotheses of the statement. The
general parametric spectral pullback implication can be proved separately
without the affinoid or group machinery.

Trivial valuations, nonreduced quotients, zero quotients, empty represented
loci and empty spectra remain permitted. No spectral maximum,
nonemptiness, separation of algebra elements by spectrum points or common
operator norm bound is assumed. The target asserts no quotient-norm
continuity of the section orbits or continuity into the automorphism
topology of `d.algebra`. It identifies no represented-domain topology with
the topology from all compact analytic domains. General analytic spaces,
structure sheaves, étale sites and cohomology remain separate obligations.
