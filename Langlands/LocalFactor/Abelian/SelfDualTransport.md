# Supplied self-dual Haar measures under field transport

This module constructs an equivalence between the existing types of supplied
self-dual Haar measures over two canonically topologized finite p-adic fields.
It also compares the existing Langlands constant and spectral epsilon expression
at corresponding witnesses. Worker 20 authored this internal compatibility
construction.

The direct import is
[`Langlands.LocalFactor.Abelian.SpectralTransport`](SpectralTransport.md).
The construction reuses the actual measure and character transports from
[`Abelian.Transport`](Transport.md) and
[`ConductorTransport`](../../HarmonicAnalysis/ConductorTransport.md),
the intrinsic Fourier self-duality transport from
[`FieldTransport`](../../HarmonicAnalysis/FieldTransport.md), and the
`SelfDualHaar` and Langlands wrappers from [`Abelian.Padic`](Padic.md).
It introduces no replacement self-duality predicate.

## Actual inputs and topology

The namespace is `Langlands.PadicField.AbelianTransport`. The fields `F` and
`E` have independent carrier universes and the same prime `p`. The supplied
map `e : F.Carrier ≃ₐ[Padic p] E.Carrier` is an actual algebra equivalence.
Both carriers use their canonical topologies and the associated Borel
measurable spaces.

The local topological instances are proved from the existing canonical data.
The local-field structure supplies local compactness and the topological ring
structure. Its compatible additive uniformity gives the Hausdorff instance.
The equality of the valuation topology with the canonical topology supplies
the nonarchimedean ring instance and hence total disconnectedness. Forward
and inverse continuity of `e` follow from the published canonical isometry
theorem. These properties are constructed; they are not additional hypotheses
on the field equivalence.

For a continuous nontrivial unitary additive character `psi`, write `psi_E`
for `ConductorTransport.additiveCharacter F E e psi`, namely inverse pullback
along `e`. For a regular additive Haar measure `mu`, write `mu_E` for
`AbelianTransport.haarMeasure F E e mu`. Its measure is the actual pushforward
`Measure.map e mu.measure`.

## The subtype equivalence

`isSelfDual_iff` specializes the published generic field-transport result:

```text
IsSelfDual psi_E mu_E <-> IsSelfDual psi mu.
```

The predicate is the intrinsic condition from
[`HarmonicAnalysis.Basic`](../../HarmonicAnalysis/Basic.md). It requires
convergence of the second Fourier integral and that Fourier squared sends
each Schwartz–Bruhat function `f` to `x ↦ f(-x)`. The Fourier kernel is
`psi(x*y)` with a positive sign. The imported transport proof changes
variables in these integrals and transports test functions by inverse
pullback. This module applies that theorem to the actual canonical field
map and the same character and measure transports used for epsilon.

`selfDualHaarEquiv` has source
`SelfDualHaar F.canonicalTopologicalData psi` and target
`SelfDualHaar E.canonicalTopologicalData psi_E`. These are the existing
subtypes of regular additive Haar measures satisfying the intrinsic
condition. The construction restricts `FieldTransport.haarMeasureEquiv`
to these subtypes using Mathlib's `Equiv.subtypeEquiv` and the preceding
equivalence of predicates. The underlying forward map is pushforward by
`e`; the inverse is pushforward by `e.symm`. The inverse laws follow from
the existing Haar-measure equivalence and subtype extensionality.

`selfDualHaarEquiv_val` and `selfDualHaarEquiv_symm_val` record those exact
underlying bundled measure maps by reflexivity. Consequently the result
transports a supplied witness and can transport one back. An equivalence
of these types asserts no inhabitant of either type, and no self-dual
measure is selected.

## Langlands values at transported witnesses

Let `chi` be any continuous complex-unit-valued quasicharacter, and let
`chi_E` be its existing inverse-pullback transport on the unit groups.
For a supplied `mu : SelfDualHaar F.canonicalTopologicalData psi`,
`langlandsConstantAtSelfDual_eq` proves equality of
`langlandsConstantAtSelfDual` at `(chi, psi, mu)` and at
`(chi_E, psi_E, selfDualHaarEquiv F E e psi mu)`.
Both values are the spectral epsilon expression at `1/2`, at the respective
supplied measures.

`langlandsEpsilonAtSelfDual_eq` gives the corresponding equality for every
complex parameter `s`, with exactly the same `s` on both sides. As in the
imported definition, this wrapper evaluates the Deligne spectral expression
at `s`. There is no additional shift of `s` in this comparison.

Both proofs apply the already published fixed-Haar spectral transport
identities, using the definitional equality of the transported underlying
measure. The half-argument constant uses `centeredConstant_eq`, and the
spectral expression uses `epsilon_eq`. The compact-shell integrals involved
have the all-parameter convergence theorem proved in `Abelian.Padic`.

## Provenance and scope

The new equivalence and identities are derived from the published input
maps, Fourier transport, subtypes and epsilon expressions. The original-source
conventions are documented with those definitions in `HarmonicAnalysis.Basic`
and `Abelian.Padic`; this module adds no external-source assertion.

The claims concern corresponding supplied measures under an invertible
algebra map. They assert neither existence nor uniqueness of a self-dual
measure, nor independence of arbitrary supplied witnesses. They also
assert no nonvanishing theorem, functional equation or unconditional
nonabelian epsilon construction. The unshifted fixed-Haar Deligne constant
and the half-argument self-dual Langlands constant remain distinct imported
constructions.
