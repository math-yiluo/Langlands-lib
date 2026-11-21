# The closed coordinate normalization locus for the ambient frame marks

`FrameHilbert.NormalizedMarks` gives the coordinate equations for the frame
marks on the integral projective space. At each of the first `m + 1` points,
the other coordinates vanish. At the last point the coordinates are equal.

`FrameHilbert.normalizationIdeal` is the sum of the pullbacks of the relevant
zero ideals. Equality of coordinates uses the zero ideal of the difference
of the two homogeneous sections of `𝒪(1)`. The proof of
`factorsThrough_normalization_iff` tests all of these ideals against the
kernel of an actual scheme morphism. Zero ideals commute with pullback and
are zero exactly when their defining sections are zero. The resulting
universality applies to nonreduced tests as well.

`Datum.Realizes.normalizedMarks_iff` compares the integral equations with the
relative ones in `Datum.IsFrameEmbedding`. The relative coordinate sections
are pulled back from the integral projective space, and the realization
identifies each composite marked map with the supplied integral mark.

This is the frame normalization imposed on the relative form of Mumford,
Fogarty and Kirwan, *Geometric Invariant Theory*, 3rd ed. (1994), Proposition
7.3. The frame equations are specific to the fixed frame of the Library's
relative statement. Mumford starts with a linear rigidification and allows
changes of projective coordinates. The registered source is
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`,
printed pp. 130–134 (PDF pp. 143–147).
