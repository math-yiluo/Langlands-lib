# Homeomorphism transport of atlas families

Author: Worker 36.

This module proves that quasinets, nets and compact Hausdorff chart families
are preserved and reflected by homeomorphisms. It also identifies the
transported restricted family using the actual subspace homeomorphism.
The ambient spaces may be non-Hausdorff and have independent universes.

## Source and provenance

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
section 1.1, printed pages 13–14 / PDF pages 10–11, defines quasinets,
restricted families, nets and the Hausdorff convention for compact sets.
Registered source: `berkovich-1993-etale-cohomology`, PDF SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
Both original pages were read for this unit. No source-specific errata
note was found in the available project and Library notes.

The homeomorphism invariance results are derived topology, not additional
assertions quoted from the source. Their purpose is to transport the
topological conditions in an existing actual affinoid atlas. The imported
definitions retain precisely the finite-neighborhood and restricted-family
conditions of section 1.1.

## Image families and finite neighborhoods

For `e : X ≃ₜ Y` and `τ : Set (Set X)`, `imageFamily e τ` consists of the
sets `e '' U` for `U ∈ τ`. `imageFamily_symm` proves that transport by
`e.symm` recovers `τ` as an equality of families.

`IsQuasinet.imageFamily` starts at `e.symm y` with a finite family `σ`
whose members contain that point and whose union is a neighborhood.
The image of `σ` under `U ↦ e '' U` is finite, belongs to the image
family and has every member containing `y`. The open-map property of
the homeomorphism carries the original neighborhood to a neighborhood
of `y`; this image is contained in the union of the transported finite
family. Upward closure of the neighborhood filter finishes the proof.
No disjointness, openness of individual family members or compactness
is needed.

## Restricted subspaces and nets

`imageFamily_restrictedFamily` proves, for every subset `S ⊆ X`,

```text
imageFamily (e.image S) (restrictedFamily τ S)
  = restrictedFamily (imageFamily e τ) (e '' S).
```

Here `e.image S : S ≃ₜ e '' S` is the homeomorphism of the actual
subspaces. For a family member `U ⊆ S`, the image of its inverse image
under subtype inclusion is the inverse image of `e '' U` under the
target subtype inclusion. Conversely, injectivity of `e` reflects
`e '' U ⊆ e '' S` to `U ⊆ S`. Explicit subtype witnesses prove both
family inclusions.

`IsQuasinet.imageFamily_restricted` transports a quasinet on that
restricted subspace by this family equality.
`IsNet.imageFamily` applies it to each intersection `U ∩ V`, using
injectivity to identify `e '' (U ∩ V)` with `e '' U ∩ e '' V`.
Together with transport of the ambient quasinet, this proves the net
condition for the image family, including overlapping members.

`isQuasinet_imageFamily_iff` and `isNet_imageFamily_iff` give the
corresponding equivalences. Their reverse directions transport back
by `e.symm` and use `imageFamily_symm`.

## Compact Hausdorff members

`IsCompactFamily.imageFamily` uses continuity to preserve compactness
of each image and `e.image U` to transport the Hausdorff instance on
each member. It does not infer Hausdorffness of the ambient space.
`isCompactFamily_imageFamily_iff` again uses inverse transport to
prove reflection.

These are family-transport results. They construct no affinoid algebras,
analytic domains, structure sheaves or sites.
