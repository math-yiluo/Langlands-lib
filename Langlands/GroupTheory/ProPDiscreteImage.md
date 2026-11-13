# Discrete images of pro-p subgroups

This internal construction connects the published
`Langlands.Cohomology.IsProPSubgroup` predicate with ordinary `IsPGroup`.
It uses actual subgroup topologies and continuous group homomorphisms,
at independent universes for the source and target.

`discreteOpenKernel` packages the kernel of a continuous homomorphism
to a discrete group as an `OpenNormalSubgroup`. Its underlying subgroup
is exactly the usual kernel. Openness follows by pulling back the open
singleton consisting of the identity; normality is the usual kernel
normality.

For a pro-p subgroup `H`, `IsProPSubgroup.isPGroup_range` applies the
defining open-normal-quotient condition to this kernel, then transports
the resulting p-group property along the first isomorphism theorem.
The surjective version uses the corresponding isomorphism to the
whole target. The image version restricts an ambient homomorphism to
`H`, whose subtype map is continuous, and identifies its range with
`H.map f`.

If every p-subgroup of the discrete target is trivial, these results
show that the range is bottom and that `H` is contained in the kernel
of the ambient homomorphism. The target need not be finite: the
definition of `IsPGroup` here is the elementwise p-power torsion
condition. Compactness of a pro-p source also forces a discrete image
to be finite, but that additional conclusion is not needed or proved
by this module.

These lemmas are elementary adapters for the reduction maps used in
the proof of KP Proposition 13.5.2. They do not establish continuity
or discreteness of a particular reductive reduction map, or prove
the proposition itself. Their provenance is the existing pro-p
definition and Mathlib's first isomorphism theorem; no new
classification result is assumed.
