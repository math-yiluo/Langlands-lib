# The frame-normalized Hilbert locus

`Langlands.AbelianScheme.PolarizedFiniteLevel.frameHilbertLocus` proves
`FrameHilbertLocusStatement`. The Lean proof applies
`frameHilbertLocus_of_pointedAbelian_and_cubicPolarization` to the
universe-zero instances of `Langlands.AbelianScheme.pointedProjectiveAbelianLocus`
and `cubicPolarizationLocus`.

The pointed locus supplies the abelian scheme of dimension `g` with the
zero mark as identity. The cubic locus supplies the polarization of degree
`d²` and the comparison of its cubic diagonal bundle with the embedding
bundle up to a base twist. The reduction imposes incidence, full level and
the frame equations, then constructs the immersion and proves the
factorization property for test realizations.
[Frame Hilbert locus reduction](FrameHilbertLocusReduction.md)

This is the relative, frame-normalized form of Proposition 7.3 of Mumford,
Fogarty and Kirwan, *Geometric Invariant Theory*, 3rd ed. (1994), printed
pp. 132–134 (PDF pp. 145–147). The registered source is
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`,
SHA-256 `3eed7c31fd64936e20a41d85c85ebaeebc3f2631b01f561417b85bdf33b1af16`.
