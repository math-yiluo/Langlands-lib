# Relative finite local refinements of nets

This module supplies a derived topological criterion for selecting members of a
net. Its source conventions are Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), §1.1, printed pp.13–14
(PDF pp.10–11), registered as `berkovich-1993-etale-cohomology`.
The retained original is
`Berkovich--Etale cohomology for non-Archimedean analytic spaces--1993.pdf`,
SHA-256 `06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
No source-specific project errata file was found when these passages were
reread. The refinement criterion is derived here from the published net axioms;
it is not attributed to a numbered theorem in the source.

`LocallyRefines υ τ` says that for every `U ∈ τ` and `x ∈ U` there is a finite
family of members of `υ`, all contained in `U` and containing `x`, whose union
is a neighborhood of `x` within `U`. These are relative neighborhoods in the
actual induced topology. The condition neither asserts ambient openness nor
assumes that `υ` is already a quasinet or net. `LocallyRefines.refl` uses the
singleton family consisting of `U`.

`IsQuasinet.refine` proves that this condition transports a quasinet from `τ`
to `υ`. At a point it takes the finite ambient neighborhood supplied by the
old quasinet, chooses a finite relative refinement inside each of its members,
and takes the union of those finite families. The identity
`nhdsWithin_sUnion` for a finite union combines the relative neighborhood
statements. Since the original union is an ambient neighborhood, the new union
is an ambient neighborhood as well. Every member of the new witness contains
the point.

`LocallyRefines.restrict` pulls the witnesses back along the inclusion of any
subspace `S`. Every chosen member stays contained in the old member and hence
in `S`, so it belongs to the actual `restrictedFamily`. Continuity of the
subtype inclusion transfers the relative neighborhood statement; a direct set
identity identifies the union of preimages with the preimage of the union.

`IsNet.of_locallyRefines` also assumes `υ ⊆ τ`. Selected pairs are therefore
old pairs, so the old intersection quasinet can be refined using
`LocallyRefines.restrict`. This proves the selected family is a net. No
Hausdorffness, compactness, openness, or intersection closure is needed for
these topological results.
