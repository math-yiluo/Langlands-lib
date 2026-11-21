# Pointed abelian presentations of marked projective families

`FrameHilbert.AbelianPresentation` records an actual abelian scheme of the
specified dimension, an isomorphism onto the closed family over its base, and
the labelled sections. The zero label agrees with the identity. This is the
output used after the abelian locus in the relative frame Hilbert problem.

`ofPointedPullback` constructs the presentation from an abelian scheme
identified with a Cartesian family. The sections are lifted by the pullback
property. `pullback` applies this construction to the actual base change of
an existing abelian scheme, giving compatibility of the embedding, sections,
and the projective twist under arbitrary base change.

An independent realization of the same family and marks yields the same
pointed scheme. The comparison isomorphism is the composite of the two
identifications with the closed family. Its compatibility with the zero mark
makes it an isomorphism of abelian schemes by pointed rigidity. The last
lemma uses the same closed-image identity to get the hypothesis on the
abelian locus of a family from a realization over a test scheme.

This interface formalizes the transition from the abelian locus to torsion
and polarization in Mumford, Fogarty and Kirwan, *Geometric Invariant
Theory*, 3rd ed. (1994), Proposition 7.3, printed pp. 132–134, PDF pp. 145–147,
registered source `provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`.
