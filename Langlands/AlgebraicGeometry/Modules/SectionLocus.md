# Global sections and their local trivialization locus

This module constructs sections and their local trivialization locus for an
arbitrary actual scheme module `M : X.Modules`, in universe `u`. No invertibility
or quasicoherence assumption is imposed in this initial construction.

`GlobalSections M` is exactly Mathlib's `Γ(M, ⊤)`. `sectionFamily M s` is the
compatible family obtained by restricting the global section to each open;
its compatibility is proved using functoriality of the underlying presheaf.
`structureModule X` is Mathlib's structure sheaf as a module over itself.
`sectionHom M s` is the module morphism corresponding to the compatible family
under Mathlib's `unitHomEquiv`; it sends one to the restricted section.

`TrivializesOn M s U` means that restriction of this morphism to the actual open
subscheme `U` is an isomorphism. Its source is the restriction of the structure
module. `trivializationOpen M s` is the supremum of all such open subsets. The
construction uses the complete lattice of opens, so it is open by construction.
`trivializationSubscheme` and `trivializationInclusion` use Mathlib's open
subscheme and its canonical inclusion. `IsStalkFrame M s x` is the separate
condition that the induced morphism on the underlying abelian-group stalks is
an isomorphism.

## Provenance and scope

These are derived infrastructure definitions motivated by the Stacks Project,
Lemma 17.25.10 (tag [01CY](https://stacks.math.columbia.edu/tag/01CY)), and the use
of `X_s` in Definition 28.27.1 (tag
[01PS](https://stacks.math.columbia.edu/tag/01PS)). The registered source is
`stacks-invertible-picard-ampleness-2026-10-21`, directory SHA256
`2a0bbd01484fc7cef97110a88cf4b3e472574fbbb9469d037170744a1462f835`, files
`01CY.html` and `01PS.html`.

The source's `X_s` is the locus where a section of an invertible module has
nonzero image in the residue-field fibre; Lemma 17.25.10 identifies it with the
locus where the section trivializes the line bundle. Here the local
trivialization locus is constructed directly for any module. No equivalence
with the residue-field condition, stalk-frame condition or a Picard invertibility
predicate is proved by this module. Those identifications are separate obligations
before this construction can be used as the source's `X_s` in ampleness.
No tensor powers, ampleness predicate or assertion that `M` is invertible is
included in this contribution.
