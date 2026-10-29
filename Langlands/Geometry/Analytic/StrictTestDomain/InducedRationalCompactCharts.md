# Compact chart nets of actual induced rational spectra

Worker 36 derives this package from the actual rational-spectrum transport
and compact coset-chart constructions. It equips the actual induced spaces
with compact Hausdorff charts and proves a criterion for their compact subsets.

## Actual carriers and topology

The hypotheses are a complete ultrametric normed field `K`, a presented strict
affinoid algebra `P`, a topological group `G`, and a
`RationalSpectralAction G P`. The field and group universes are independent.
For an object `X : ρ.OpenSubgroupTransport`, its stored subgroup `H` is open,
its `LocalSpectrum` is the actual Banach spectrum of its rational closed-ideal
Tate quotient algebra, and its `InducedSpectrum` is the balanced quotient
`G ×_H X.LocalSpectrum` with the constructed continuous actions.

The new `CompactSpace X.LocalSpectrum` and `T2Space X.LocalSpectrum` instances
reuse the existing proofs in `Spectrum.Properties`. In that module evaluation
embeds the spectrum into the product of real lines as a closed subset of the
product of compact intervals `[0, ‖a‖]`. These proofs require no nonemptiness
assumption. Unfolding the actual carrier and topology supplies the instances;
compactness and Hausdorffness are not fields assumed of a rational action.

The stored subgroup openness and these spectrum instances specialize
`TopologicalInduction.t2Space_induced` and
`TopologicalInduction.locallyCompactSpace_induced`. This gives Hausdorffness
and local compactness of `X.InducedSpectrum`. The first proof uses the
constructed homeomorphism from the coproduct of coset copies; the second
uses the compact quasinet. No separation assumption on the group is needed.

## The compact net and chart subspaces

`X.inducedChartFamily` is the actual family of fibers

`c ↦ X.inducedComponent ⁻¹' {c}`, for `c : G/H`.

It specializes `TopologicalInduction.cosetChartFamily`. Each fiber belongs,
as does every actual open subset `X.inducedChartDomain a`: that subset is
the range of the chart `x ↦ [a,x]`, equal to the fiber over `aH`.

`isNet_inducedChartFamily` specializes the proved coset-fiber net. Its
quasinet witness at a point is the singleton consisting of that point's open
fiber. At a point in the intersection of two fibers the labels coincide,
and the common fiber restricts to the entire intersection.
`isCompactFamily_inducedChartFamily` also proves that each member is compact
and Hausdorff with its actual subspace topology. Compactness is supplied by
the continuous image of the actual compact rational quotient spectrum.

`isCompact_inducedComponent_fiber` and `isCompact_inducedChartDomain` expose
the compact-subset conclusions. The resulting `CompactSpace` instance on
each `inducedChartDomain a` is the standard equivalence between compactness
of a subset and compactness of its subtype. Hausdorffness of those subspaces
is inherited from the proved Hausdorff induced space. The existing
`inducedChartHomeomorph` identifies each with the actual rational quotient
spectrum.

## Compact subsets and transport

`finite_inducedComponent_image_of_isCompact` proves that a compact subset
has finitely many coset labels. It applies the generic theorem mapping
compact subsets continuously into the discrete coset quotient.
`exists_finite_inducedChart_cover_of_isCompact` supplies a finite collection
of cosets whose chosen-representative chart domains cover that subset.
Neither result asserts that the whole coset quotient is finite.

`isCompact_iff_isClosed_finite_inducedComponent_image` proves

`IsCompact s ↔ IsClosed s ∧ (X.inducedComponent '' s).Finite`.

The forward implication uses Hausdorffness and the finite-image result.
For the converse the component image is finite, so the union of the fibers
with labels in that image is compact. Every point of `s` belongs to its own
fiber. Since `s` is closed, it is a closed subset of that compact union and
is compact. This proof includes the empty subset and empty local spectra.

For a transport arrow `f : X ⟶ Y`,
`Hom.inducedComponent_image_inducedMap` proves the exact set equality

`Y.inducedComponent '' (f.inducedMap '' s)
  = f.cosetMap '' (X.inducedComponent '' s)`.

It rewrites both iterated images and uses the already proved component
triangle pointwise. `finite_inducedComponent_image_inducedMap` follows by
the image of a finite set under the actual coset map. These conclusions use
the existing transport map with its inverse-label correction. They make no
properness claim about transport between different subgroups.

## Provenance and scope

This is an internal derived construction over the published
`InducedRationalCharts`, `Spectrum.Properties`, and
`Topology.GroupAction.InducedCompactCharts` APIs. The compactness criterion
and transport formula are additional elementary deductions from those APIs.
The imported compactness proof is documented in `Spectrum/Properties.md`;
this unit uses the proved instances rather than a separate spectrum
existence assertion.

Berkovich, *Etale cohomology for non-Archimedean analytic spaces* (1993),
section 1.1, printed pages 13–14 (PDF pages 10–11), supplies the quasinet,
net and compact Hausdorff conventions used by the imported topology.
The registered source is `berkovich-1993-etale-cohomology`, PDF SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The actual left-coset-copy convention follows Berkovich's unfinished
*Etale equivariant sheaves on p-adic analytic spaces* (1995–1996),
`Equish_1996` manuscript, Construction 1.1.2, printed/PDF page 2, through
the imported induced charts. The registered folder is
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`,
member PDF SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The originals were read during development of the imported construction.
The compactness criterion and transport-image equality here are derived
results, not quotations from either source.

These are topological compact chart domains on actual rational spectra.
Analytic atlas compatibility, structure-sheaf descent, analytic morphisms,
distinguished domains, etale and quasi-etale sites, induction in stages,
and the Harris tower specialization remain separate obligations.
