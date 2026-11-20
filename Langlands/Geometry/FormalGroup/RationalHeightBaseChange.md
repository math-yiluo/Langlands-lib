# Base change of local rational height presentations

For a section of the rational formal Hom sheaf on an open of an affine
spectrum, a height presentation consists of an actual integral numerator
and a scalar-power denominator. Both kernels have specified constant
ranks. The presentation index is the difference of their logarithmic
ranks, as in Harris's Appendix, printed p. 112.

`HeightPresentation.baseChange` pulls back the integral numerator along
the coefficient square for the open and its inverse image. The canonical
formal isomorphisms in this square preserve the numerator rank after
extension. The scalar endomorphism also pulls back to that same scalar
on the new source. The section equality follows from linearity of the
sheaf pullback and its formula on actual integral sections. The two
specified rank exponents are retained. `HasHeightFunction.baseChange`
pulls back the witnessing neighborhoods and the height function along
the actual map of spectra. The coefficient map can be arbitrary.

`HeightPresentation.transportIso` applies actual integral coordinate
changes on source and target. It presents the section defined by
conjugation, using the integral coordinate changes to transport the
numerator kernel and the scalar denominator kernel. The index is
preserved, and the formula also holds for heights defined locally by
such presentations.

These are derived transport constructions for the coefficient changes
and integral identifications of Harris's (A.4). They use the actual
coefficient maps and kernel-rank preservation.

- Michael Harris, *Supercuspidal representations in the cohomology of
  Drinfel'd upper half spaces*, Invent. Math. 129 (1997), Appendix,
  printed p. 112 (PDF p. 38) for the height formula and (A.4), printed
  p. 114 (PDF p. 40) for the structural coefficient twist.
