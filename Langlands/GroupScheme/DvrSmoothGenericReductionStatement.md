# Finite covers with smooth generic fibre

Worker 572.

`Langlands.GroupScheme.DvrSmoothGenericReductionStatement.{u}` is a
proposition definition. It records the preliminary reduction in the
proof of Brian Conrad's Corollary A.4, before stable normalization.
There is no proof in this module.

The input is any actual flat, separated, finite-type group scheme `G`
over an arbitrary DVR `R`, together with any fraction field `K` whose
actual generic fibre of `G` is affine. Finite type is expressed by
`LocallyOfFiniteType` and `QuasiCompact`. The original group need not
be reduced, smooth, connected or commutative.

The conclusion is a same-universe DVR `R'`, a flat surjective actual
base morphism `b : Spec R' → Spec R`, and an actual flat, separated,
finite-type group scheme `P` over `R'`. An actual group-scheme
homomorphism `q : P → b*G` is finite and surjective on underlying
schemes. The actual generic fibre of `P`, formed over
`FractionRing R'`, is both smooth and affine. The statement asserts no
smoothness for the total group `P`, and it specifies no canonical
normalization or finite degree for the base extension.

## Provenance

This is a derived interface for the first step of Corollary A.4 in
Conrad's appendix to Prasad and Yu, *On quasi-reductive group schemes*,
author-preprint p.29. Its proof first extends the fraction field until
the reduction of the generic group is geometrically reduced and hence
smooth. The flat reduced total scheme is a closed subgroup, because
its square is flat with reduced generic fibre and therefore reduced.
The reduction inclusion is finite and surjective. Its generic fibre
is affine as a closed subscheme of the affine generic fibre of `G`.

An equivalent construction uses the schematic closure of that smooth
reduced generic subgroup. Flatness of `G` makes its generic fibre
dense, so the closure inclusion is surjective. This construction
still supplies exactly the properties recorded here.

For a local DVR extension throughout, first use a faithfully flat
henselian DVR extension as in Proposition 3.1, p.5; Remark A.1, p.28,
ensures the integral closure in the finite fraction-field extension
is again a DVR. The field-extension reduction itself is the first
clause of Theorem A.2, p.28, and the coefficient-descent step in the
proof of Lemma A.5, p.29. The interface forgets the particular
reduction/closure construction and retains actual maps and their
properties. Obtaining a smooth total covering group requires the
separate stable-normalization argument in the remainder of A.4.

Registered source:
`prasad-yu-2006-quasi-reductive-author-preprint`, SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`,
*Prasad–Yu, On quasi-reductive group schemes (author preprint).pdf*.
