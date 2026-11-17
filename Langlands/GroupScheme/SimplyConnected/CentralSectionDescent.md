# Descent of sections of central extensions of perfect field groups

`CentralSectionDescent.sectionHom` descends a supplied homomorphic section
after an affine, flat, surjective, quasi-compact change of base
`p : S ⟶ Spec k`. The original homomorphism is `q : H ⟶ G`, both groups
are affine over the field, its full kernel is central, and the full
scheme-theoretic derived subgroup of `G` equals `G`.

`CentralSectionDescent.compatible` proves that any such section respects
the canonical descent data. On the double overlap, the two pullbacks of
the section, with their canonical endpoint identifications, have the same
composite with the pulled-back quotient. The overlap source remains
perfect by arbitrary-affine base change for derived groups and the
direct/iterated pullback isomorphism. The pulled-back kernel is central
and affine, hence separated. Perfect-source cancellation through this
central kernel identifies the two pullbacks on the whole overlap scheme,
including its possible nilpotents.

The definition then applies `Descent.FpqcHomDescent.hom` to these compatible
maps. `baseChange_sectionHom` recovers the supplied section, and
`sectionHom_comp` reflects the section identity through faithful fpqc
pullback. `exists_section` packages existence of the descended section.

## Provenance

This is an internal derived construction. It combines
`Derived.CentralKernelCancellation`, functoriality of the full derived
subgroup, canonical Čech data, and the published fpqc homomorphism-descent
construction. Its proof checks compatibility on the actual scheme
overlap; no reducedness or separability of the cover is assumed.
Centrality of the full original kernel is an explicit hypothesis.
