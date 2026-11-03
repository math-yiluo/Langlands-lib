# Spreading a specified fibre-ample line bundle

`Langlands.AlgebraicGeometry.Picard.ProperFibreAmpleSpreadingStatement`
states a fixed-bundle spreading result in every universe. Let
`f : X ⟶ S` be proper, with `S` locally noetherian, and let `L` be an
actual line bundle on `X`. If its actual pullback to the scheme-theoretic
residue-field fibre at an arbitrary point `s : S` is ample, there is an
affine open neighbourhood `V` of `s` such that the actual restriction of
this same `L` to `f ⁻¹ᵁ V` is ample.

The affine open is an output. The result has no flatness, reducedness,
closed-point, field or characteristic hypothesis. In particular, the
fibre is neither reduced nor replaced by a geometric fibre, and the
conclusion concerns the specified bundle, rather than the existence of
some other ample bundle.

## Source and derivation

This is the affine-neighbourhood form of Stacks Project
[Lemma 37.50.3, tag 0D2S](https://stacks.math.columbia.edu/tag/0D2S),
together with
[Lemma 29.38.5, tag 01VK](https://stacks.math.columbia.edu/tag/01VK).
The first result spreads relative ampleness of the specified bundle from
one fibre. Shrink that neighbourhood to an affine open containing the
point; relative ampleness restricts to base opens. The second result
identifies relative ampleness with ampleness on the source over that
affine base. Local noetherianity is a retained restriction for the
intended consumer; the cited spreading lemma holds over arbitrary bases.

Both primary HTML pages, including their proofs and comments, were read
in the registered source
`stacks-fibre-ampleness-affine-neighbourhood-2026-11-02`, content SHA256
`7a654789470ca2c545023588c4949fa09b3559b6801d9ff2f7c74b826eadc3a3`.
The files are `0D2S.html` and `01VK.html` in
`literature/Stacks Project - Fibre ampleness and local projectivity (HTML snapshot 2026-11-02)`.
No source-specific errata file was present in the checked workspace,
current Library or project `notes/errata` locations. The source's
reference to EGA IV.3, Corollary 9.6.4 does not assert that the EGA
original was read.

## Role in the affine-neighbourhood argument

This is a substantial missing geometric prerequisite for
`ProperFibreAmpleAffineOpenStatement`. After spreading, a finite set over
`s` remains inside the restricted total space. A finite-set affine
neighbourhood theorem for ample schemes can then supply the desired
affine open, whose image under the open immersion into `X` is affine.
This route avoids constructing a projective embedding.

The Lean file only defines the proposition. It proves neither
spreading nor the finite-set affine-neighbourhood result and makes no
representability claim.
