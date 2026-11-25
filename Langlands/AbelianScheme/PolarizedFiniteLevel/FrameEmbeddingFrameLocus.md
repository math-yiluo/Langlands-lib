# A normalized cubic embedding has the whole base as frame locus

`Datum.IsFrameEmbedding.frameLocus_eq_top` works for the cubic projective
dimension on a locally noetherian base with `0 < d`. The proof checks the
joint evaluations after passing to an algebraic closure of each residue
field, then uses the proved compatibility of the frame locus with base
change.

Over the field, `Datum.IsFrameEmbedding.twistIsoCubicOverField` uses a chosen
trivialization of the base twist. This identifies the pullback of `𝒪(1)` with
the cubic bundle, so the homogeneous coordinates give sections of it. In
each of the first `m + 1` evaluations only the matching coordinate is
nonzero. All coordinates of the last evaluation are nonzero since they
agree and some coordinate is nonzero at every projective point. The first
`m + 1` evaluations give linear independence of the coordinate sections.
The cubic section dimension `m + 1` then gives a basis.

If the last evaluation is omitted, every coefficient in that basis is
still detected by its own evaluation. If a different evaluation is omitted,
all but one coefficient are detected by the remaining basis points, and
the last evaluation detects the remaining coefficient. Joint evaluation is
injective in each case and the equal dimensions give surjectivity. This
proves all the frame evaluations are isomorphisms in the geometric fibres.

This is the frame-specific linear algebra used for the frame-normalized Hilbert
locus (`FrameHilbertLocusStatement`; module `FrameHilbertLocusReduction`) in the relative
analogue of step (VI) of Mumford, Fogarty and Kirwan, *Geometric Invariant
Theory*, 3rd ed. (1994), Proposition 7.3, printed p. 134 (PDF p. 147),
registered source `provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`.
