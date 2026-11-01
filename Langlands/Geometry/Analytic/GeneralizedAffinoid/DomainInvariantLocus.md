# Equivariant quotient presentations of actual represented loci

Author: Worker 56.

## Setting

Let `K : Type u` be a complete ultrametric normed field, let
`P : PresentedAffinoidAlgebra K` be an actual finite positive-polyradius
affinoid quotient, and let `G : Type v` be a topological group. Fix
`ρ : DomainSpectralAction G P`, an action by actual bounded algebra
automorphisms continuous for the explicit represented-domain spectral
topology. The two universes remain independent. All declarations are in
the namespace
`PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction`.

For an open subgroup `H`, an object `d : ρ.InvariantDomain H` retains an
actual domain section algebra, its bounded structural map from `P`,
its closed locus in `BanachSpectrum P`, and its full representation
property against every presented affinoid. Its invariance witness says
that every element of `H` preserves that locus setwise.

## The represented-locus action

`invariantLocusOperator H d g` restricts the original inverse-pullback
operator on the ambient spectrum to the closed subspace `d.obj.locus`.
Its underlying ambient point is exactly

```text
ρ(g) • x,       (ρ(g) • x)(a) = x(ρ(g).inv(a)).
```

Setwise invariance proves that this point is in the locus. The ambient
bounded inverse map gives a continuous spectrum pullback, so the
restriction is continuous for each fixed `g : H`. `invariantLocusAction`
packages these operators into `Action TopCat H`. The identity and
multiplication laws follow from the existing ambient action after
applying subtype extensionality.

`invariantLocusActionFunctor` realizes the full category of invariant
domain representations by these locus actions. Each arrow is the original
continuous locus inclusion obtained from its actual bounded restriction.
Both ways around its equivariance square give the same ambient point.
The identity and composition laws likewise retain the underlying points.
Forgetting the action gives exactly the published `Domain.locusFunctor`
precomposed with the full invariant-domain inclusion.

## Actual equivariant quotient maps

`invariantSpectrumToLocus H d` has underlying map
`d.obj.spectrumToLocus`: it pulls a seminorm on the section algebra back
along the bounded structural map and records membership in the represented
locus. The source is the previously constructed action on the actual
section spectrum; the target is the restricted ambient locus action.

Its equivariance follows from `spectrumMap_smul`, which in turn uses
the equality of full bounded structural composites for the constructed
section action at the inverse group element. In particular this comparison
does not require spectrum points to distinguish nilpotent algebra
elements.

The structural representation property gives surjectivity onto the locus.
The existing domain topology theorems give that the map is closed and is a
quotient map for the actual subspace topology. The corresponding three
lemmas expose these facts for the equivariant morphism. They do not assert
injectivity of the structural map on section spectra.

For each bounded domain restriction, the original
`spectrumToLocus_naturality` equation supplies the commuting equivariant
square. `invariantSpectrumToLocusNatTrans` packages all these structural
quotients as a natural transformation. Its forgetful theorem identifies
the entire transformation with the published structural transformation
restricted to invariant domains, by definitional equality.

## Provenance and scope

This is an internal construction from the existing full domain
representations, stabilizer section actions, bounded restriction
compatibilities, and compact quotient topology results. The proof uses
only these constructions and Mathlib's categorical action packaging.
No new literature result is attributed.

The construction allows empty loci and spectra, zero quotients,
nilpotents, and trivial scalar valuations. `Action TopCat H` requires a
continuous operator for each fixed group element; no joint continuity
theorem is asserted. Finite invariant covers can use these quotient
presentations, but analytic gluing, structure sheaves, analytic etale
sites, and the Harris specialization remain further work.
