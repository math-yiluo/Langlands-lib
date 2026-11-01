# Continuous spectrum and locus quotient diagrams over the actual base

Authors: Worker 56; Worker 36, whose strict rational overcategory construction
supplies the structural spectrum diagram pattern adapted here.

Let `K : Type u` be a complete ultrametric normed field, let `P` be an actual
finite positive-polyradius presented affinoid quotient over `K`, and let
`G : Type v` be a topological group. The two universes are independent.
Fix `ρ : DomainSpectralAction G P` and an open subgroup `H`. Continuity
into the existing represented-domain spectral automorphism topology is
the input; joint continuity on actual spectra and invariant loci is
already proved by the imported constructions.

`restrictedGlobalSpectrum` restricts the jointly continuous global action
along the continuous subgroup inclusion `H → G`. Its underlying action
is exactly `restrictedGlobalSpectrumAction`. It retains `BanachSpectrum P`
with the original topology and the inverse-pullback operator
`(g • x)(a) = x ((ρ(g : G)).inv(a))`.

`invariantSpectrumToBase` lifts the existing equivariant structural
spectrum pullback through the full subcategory of continuous actions.
Its value at `x : BanachSpectrum d.obj.algebra` is exactly
`d.obj.spectrumMap x`, whose evaluation at `a : P` is
`x (d.obj.baseMap a)`. All actual bounded domain arrows retain their
original commuting structural triangles, by
`invariantSpectrumToBase_naturality`. The proof uses the preceding
equation of action morphisms, derived from each bounded restriction's
structural-map equation.

`invariantLocusToBase` is the continuous subtype inclusion from
`d.obj.locus` to the original spectrum. Its equivariance follows directly
from the definition of the restricted ambient action. Locus restrictions
retain their spectrum points, giving
`invariantLocusToBase_naturality`. The equation
`invariantSpectrumToLocusContinuous_over_base` states that the actual
structural quotient followed by this inclusion equals the structural
spectrum pullback. The proof evaluates the two concrete maps.

The two structural natural transformations to the constant base action
give `invariantSpectrumOverFunctor` and `invariantLocusOverFunctor` by
Mathlib's `Over.lift`. Both diagrams have target
`Over (ρ.restrictedGlobalSpectrum H)`, so their objects retain actual
maps to the same continuous base action. Their arrows retain every
bounded domain restriction and locus inclusion, respectively.
`invariantSpectrumToLocusOverNatTrans` is the structural quotient
transformation in this overcategory. Its components are exactly
`invariantSpectrumToLocusContinuous`; the factorization above is their
overcategory equation. Its naturality is the established quotient
square after extensionality of overcategory morphisms.

The projection formulas identify both diagrams' object structural maps
and arrow components. Forgetting the structural maps recovers the
continuous spectrum and locus diagrams. Further forgetting actions
recovers the original topological diagrams on the full invariant domain
category. Forgetting joint continuity from the spectrum overcategory
recovers the preceding `invariantSpectrumActionOverFunctor`.
Whiskering the overcategory quotient transformation with the
overcategory forgetful functor gives the preceding continuous quotient
transformation. These identities are definitional.

This is an internal categorical construction on the existing actual
bounded structural maps and locus inclusions. It adapts the spectrum
part of Worker 36's `StrictTestDomain/SpectralOverBase`, then adds the
locus diagram and structural quotient factorization over the same base.
Joint continuity is derived by the imported local and global proofs,
not assumed for a new output object. No new literature theorem is
asserted. The existing surjective closed quotient properties apply to
the same component maps; no spectrum injectivity is claimed.

Empty loci and spectra, zero quotients, nilpotents and trivial scalar
valuations remain allowed. Comparison with all compact analytic-domain
tests, analytic atlases and structure sheaves, analytic etale sites
and the Harris specialization remain further work.
