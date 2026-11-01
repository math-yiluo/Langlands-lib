# Jointly continuous finite spectrum quotient covers

Authors: Worker 56; Worker 36, whose strict rational common-stabilizer
construction supplies the finite-intersection pattern in the imported
finite-cover support.

Let `K : Type u` be a complete ultrametric normed field, let `P` be an
actual finite positive-polyradius presented affinoid quotient over `K`,
and let `G : Type v` be a topological group. The group and field universes
are independent. Fix `ρ : DomainSpectralAction G P`, an open subgroup `H`,
an invariant represented domain `d : ρ.InvariantDomain H`, and a supplied
actual finite cover `c : Domain.FiniteCover d.obj`.

The previously constructed open subgroup
`J = ρ.finiteFamilyOpenSubgroup H c.obj` is the intersection of `H` with
the open locus stabilizers of all original cover components. The
existing `finiteCoverSpectrumAction` acts on the actual topological
disjoint union

```text
Σ i : Fin c.size, BanachSpectrum (c.obj i).algebra.
```

It fixes the component index and uses the constructed inverse bounded
section pullback on that component's spectrum.

`finiteCoverSpectrumAction_isContinuous` proves joint continuity of this
same action. For each component it applies the proved
`invariantSpectrumAction_isContinuous` at `J`. Swapping the spectrum and
group coordinates and composing with the continuous summand inclusion
gives a continuous map on that component spectrum times `J`.
The disjoint-union continuity criterion assembles these maps on
`Σ i, BanachSpectrum (c.obj i).algebra × J`. Finally the homeomorphism
`Homeomorph.sigmaProdDistrib`, after swapping coordinates, identifies the
original group-times-disjoint-union source with this source. Composition
gives exactly the existing joint action. This proof needs no nonempty
index or spectrum assumption.

`finiteCoverSpectrum` packages this action and proof as
`ContAction TopCat J`. The forgetting and operator formulas identify the
unchanged original action. `finiteCoverComponentContinuous` lifts each
existing equivariant component map through the full subcategory of
jointly continuous actions. Its actual map is exactly
`c.componentMap i`: structural spectrum-to-locus quotient followed by
the original bounded domain arrow's locus inclusion.

`finiteCoverQuotientContinuous` lifts the existing equivariant quotient.
Its target is the original target locus with its proved jointly
continuous restricted ambient action. Its underlying continuous map is
exactly `TopCat.ofHom c.totalMap`. The exposed surjectivity, closedness
and quotient-map theorems reuse those properties of this exact map and
the target's actual subspace topology. The openness and closedness
criteria test preimages on the unchanged component maps. The
continuity criterion allows an arbitrary topological target `Y : Type w`
and imposes no equivariance condition on the function being tested.

The provenance is internal. The proof combines established component
joint continuity, Mathlib's product/disjoint-union homeomorphism and the
existing concrete finite-cover action. The quotient lift retains the
existing maps, equivariance equations and topological conclusions.
No additional literature theorem or continuity premise is asserted.
The finite-intersection support adapts Worker 36's strict rational
construction; the present continuity argument uses the full represented
domain spectra over positive polyradii.

The cover may be empty when the target locus is empty. Zero quotients,
nilpotents, empty spectra and trivial scalar valuations remain allowed.
The quotient is onto the target locus; no surjectivity onto its section
spectrum or spectrum injectivity is asserted. Algebra-section descent,
analytic atlases, structure sheaves, analytic etale sites and the Harris
specialization remain further constructions.
