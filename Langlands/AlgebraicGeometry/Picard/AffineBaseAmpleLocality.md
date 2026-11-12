# Globalizing ampleness from principal neighbourhoods

This internal construction is derived directly from the Library's section-open definition of ampleness. A line bundle on a compact quasi-separated scheme is ample if its restriction is ample on principal open neighbourhoods of all points.

The proof converts a positive-power section on a principal open to a section of the original tensor power over that open, then clears its denominator using `PrincipalSectionExtension.exists_global`. The cleared section has the same generation open on the principal open because the denominator is a unit there. Tensoring once with the defining global function cuts its whole generation open down to that principal open. This open is the image of the original affine section open, hence affine. The exponent of the line bundle remains positive and unchanged.

The supporting lemmas verify bijectivity of the actual open-section conversion, compatibility with restriction of global sections, and invariance of generation opens under unit multiplication. This construction supplies only the globalization step; it does not prove specialization of ampleness between fibres.

Over an affine base, `LineBundle.isAmple_of_affine_base_neighbourhoods`
reduces neighbourhoods of base points to principal open neighbourhoods on
the total space. An affine basic-open refinement of each base neighbourhood
pulls back to a principal open defined by a global function on the total
space. Its inclusion into the original inverse-image neighbourhood is
affine, so the Library's affine-pullback theorem preserves ampleness there.
The principal-neighbourhood result then applies.

For a proper morphism to a locally noetherian affine base,
`LineBundle.isAmple_of_fibrewise_over_affine` uses the published
`properFibreAmpleSpreading` theorem to obtain these neighbourhoods from
ampleness on every residue-field fibre. Properness and affineness of the
base supply compactness and quasi-separatedness of the total space.
The corollary concerns a specified total line bundle; it constructs no
line bundle and assumes ampleness on all fibres.
