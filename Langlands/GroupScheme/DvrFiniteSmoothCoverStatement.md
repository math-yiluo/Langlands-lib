# A finite smooth cover after a DVR extension

`Langlands.GroupScheme.DvrFiniteSmoothCoverStatement.{u}` is a proposition
definition. This module supplies an interface and no proof.

For an actual flat, separated, finite-type group scheme `G` over a DVR
`R`, with affine actual generic fibre over a specified fraction field
`K`, it asserts the existence of:

- a DVR `R' : Type u` and a flat surjective morphism
  `b : Spec R' → Spec R`;
- an actual smooth, quasi-compact, separated group scheme `H` over `R'`
  with affine actual generic fibre over `FractionRing R'`;
- an actual group-scheme homomorphism `π : H → b*G` whose underlying
  scheme morphism is finite and surjective.

The base morphism is between affine spectra, hence quasi-compact.
Together with flatness and surjectivity it is an fpqc cover. This
formulation does not prescribe a particular ring extension, normalization,
or reduction construction. It does not assert that `H` is already affine.
All rings and schemes have the arbitrary universe `u`. No smoothness or
connectedness is required of the original group.

## Provenance and source comparison

This is a derived consequence of Brian Conrad's appendix to Gopal Prasad
and Jiu-Kang Yu, *On quasi-reductive group schemes*, especially Corollary
A.4, author-preprint p.29, with the henselian reduction of Proposition
3.1 on p.5 and the integral-closure discussion in A.1 on p.28.

The source first allows a faithfully flat henselian DVR extension.
After a finite extension of its fraction field, the reduced base change
is a subgroup and its normalization is finite and smooth. Over the
henselian DVR the integral closure in the chosen finite field extension
is again a DVR. The composite from the normalization through the
reduction to the original base-changed group is finite and surjective.
Its generic fibre is affine because it is finite over the affine
base-changed generic fibre. Separatedness and finite type of the covering
group follow from the finite map and the original separated finite-type
group. The present statement records these consequences and omits the
canonical normalization identity and persistence under further base
extensions asserted in A.4.

The interface is intended for reduction to the separately stated smooth
DVR affineness criterion, followed by finite-surjective and fpqc descent
of affineness. It is independent of the assertion that the original
group is affine; proving that assertion is not part of this definition.

Registered source:
`prasad-yu-2006-quasi-reductive-author-preprint`, SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`,
file *Prasad–Yu, On quasi-reductive group schemes (author preprint).pdf*.
