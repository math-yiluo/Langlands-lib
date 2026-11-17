# Potential geometric reducedness of the reduced generic fibre

Worker 572.

`Langlands.AlgebraicGeometry.DvrPotentialGenericReductionStatement.{u}`
is a proposition definition, with no proof in this module. It concerns an
actual flat finite-type scheme over any DVR `R : Type u`. Finite type is
expressed by `LocallyOfFiniteType` and `QuasiCompact`. There is no
separatedness, reducedness, smoothness, or group assumption.

The conclusion provides a same-universe DVR `R'`, together with an actual
flat surjective morphism `b : Spec R' → Spec R`. First pull back `X` along
`b`, then pull back along the actual fraction-field morphism
`Spec (FractionRing R') → Spec R'`, and finally take the canonical reduced
closed subscheme. The resulting scheme over `FractionRing R'` is
geometrically reduced. The order of these operations is part of the
statement: reduction is performed after both base changes.

The helper `DvrPotentialGenericReduction.reducedOver` defines this
canonical reduction as the closed subscheme cut out by the vanishing
ideal of the whole underlying space, composed with the original
structural map. It adds no supplied geometric hypothesis.

## Provenance

This is a scheme-level consequence of Brian Conrad's appendix to
Gopal Prasad and Jiu-Kang Yu, *On quasi-reductive group schemes*,
Theorem A.2, author-preprint p.28, and the first coefficient-descent
step in the proof of Lemma A.5, p.29. A.2 makes the generic fibre of
the reduced base change geometrically reduced after a finite extension
of the fraction field. Reduction commutes with localization, so its
generic fibre is the reduction of the actual generic fibre used here.

For a DVR, one may first pass to a faithfully flat henselian DVR
extension, as in Proposition 3.1, p.5. By Remark A.1, p.28, the integral
closure of that henselian DVR in the finite fraction-field extension
is again a DVR. The composite map on spectra is flat and surjective.
This yields precisely the extension allowed by the interface; it does
not require the map of DVRs itself to have finite degree. The rings,
field extensions and schemes can all be constructed in the original
universe. The statement deliberately records only potential geometric
reducedness, without any normalization, group law, or smooth model.

Corollary A.4, p.29, uses this preliminary step before constructing the
smooth generic reduction of a group scheme. That group construction
and the extension of its operations are separate obligations.

Registered source:
`prasad-yu-2006-quasi-reductive-author-preprint`, SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`,
*Prasad–Yu, On quasi-reductive group schemes (author preprint).pdf*.
